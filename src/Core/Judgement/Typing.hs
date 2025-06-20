module Core.Judgement.Typing (inferType, checkType) where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation

import Data.Bifunctor (second)
import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString)

-- This context records the type of bound variables, where the ith type in the
-- context is the type of the ith binder away from the current term
type BoundContext = [(Maybe ByteString, Term)]

type TypeCheck a = ReaderT (Environment, BoundContext, Context) CanError a

inferType :: Environment -> Context -> Term -> CanError Term
inferType env ctx m = runReaderT (runInferType m) (env, [], ctx)

checkType :: Environment-> Context -> Term -> Term -> CanError Term
checkType env ctx m t = runReaderT (runCheckType m t) (env, [], ctx)

runInferType :: Term -> TypeCheck Term
runInferType (Univ i)                                   = return $ Univ (i + 1)
runInferType Star                                       = return One
runInferType Zero                                       = return $ Univ 0
runInferType One                                        = return $ Univ 0

runInferType (Var (Bound i))                            = do
  (_, bctx, _) <- ask

  if i >= 0 && i < length bctx
  then return $ snd $ bctx !! i
  else typeError FailedToInferType (Just ("Invalid index for bound term \"" ++ show i ++ "\""))

runInferType (Var (Free x))                             = do
  (_, _, ctx) <- ask

  case lookup x ctx of
    Just t  -> return t
    Nothing -> typeError FailedToInferType (Just ("Unknown variable " ++ show x))

runInferType (Pi (x, t) m)                              = do
  (_, bctx, _) <- ask

  tt <- runInferType t
  mt <- local (addToBoundCtx (x, t)) (runInferType m)

  case (tt, mt) of
    (Univ i, Univ j) -> return $ Univ $ max i j
    (Univ i, _)      -> typeError TypeMismatch (Just (showTermWithContext bctx m ++ " is not a term of a universe"))
    (_, _)           -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

runInferType (Sigma (x, t) m)                           = do
  (_, bctx, _) <- ask

  tt <- runInferType t
  mt <- local (addToBoundCtx (x, t)) (runInferType m)

  case (tt, mt) of
    (Univ i, Univ j) -> return $ Univ $ max i j
    (Univ i, _)      -> typeError TypeMismatch (Just (showTermWithContext bctx m ++ " is not a term of a universe"))
    (_, _)           -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

runInferType (Lam (x, Just t) m)                        = do
  (_, bctx, _) <- ask

  tt <- runInferType t
  mt <- local (addToBoundCtx (Just x, t)) (runInferType m)

  case tt of
    Univ i -> return $ Pi (if isBinderUsed mt then Just x else Nothing, t) mt
    _      -> typeError TypeMismatch (Just (showTermWithContext bctx t ++ " is not a term of a universe"))

runInferType (Lam (x, Nothing) m)                       = do
  (_, bctx, _) <- ask

  typeError FailedToInferType (Just ("Cannot infer type of implicit lambda " ++ showTermWithContext bctx (Lam (x, Nothing) m)))

runInferType (App m n)                                  = do
  (env, bctx, _) <- ask

  mt <- runInferType m
  nt <- runInferType n

  case mt of
    Pi (x, t) t' -> if equal env t nt
      then return $ shift (-1) $ open (bumpUp n) t'
      else typeError TypeMismatch (Just (showTermWithContext bctx m ++ " of type " ++ showTermWithContext bctx mt ++ " cannot be applied to " ++ showTermWithContext bctx n ++ " of type " ++ showTermWithContext bctx nt))
    _            -> typeError TypeMismatch (Just (showTermWithContext bctx m ++ " is not a term of a Pi type") )

runInferType (Pair m n)                                 = do
  mt <- runInferType m
  nt <- runInferType n

  return $ Sigma (Nothing, mt) nt

runInferType (Sum m n)                                  = do
  (_, bctx, _) <- ask

  mt <- runInferType m
  nt <- runInferType n

  case (mt, nt) of
    (Univ i, Univ j) -> return $ Univ $ max i j
    (Univ i, _)      -> typeError TypeMismatch (Just (showTermWithContext bctx n ++ " is not a term of a universe"))
    (_, _)           -> typeError TypeMismatch (Just (show m ++ " is not a term of a universe"))

runInferType (Inl m)                                    = do
  (_, bctx, _) <- ask

  typeError FailedToInferType (Just ("Cannot infer type of ambiguous injection " ++ showTermWithContext bctx (Inl m)))

runInferType (Inr m)                                    = do
  (_, bctx, _) <- ask

  typeError FailedToInferType (Just ("Cannot infer type of ambiguous injection " ++ showTermWithContext bctx (Inr m)))

runInferType (IdFam t)                                  = do
  (_, bctx, _) <- ask

  tt <- runInferType t
  case tt of
    Univ i -> return $ Pi (Nothing, t) $ Pi (Nothing, t) tt
    _      -> typeError TypeMismatch (Just (showTermWithContext bctx t ++ " is not a term of a universe"))

runInferType (Id Nothing m n)                           = do
  (env, bctx, _) <- ask

  mt  <- runInferType m
  mtt <- runInferType mt
  nt  <- runCheckType n mt

  return mtt

runInferType (Id (Just t) m n)                          = runCheckType (Id Nothing m n) t

runInferType (Refl m)                                   = return $ Id Nothing m m
  
runInferType (Ind Zero (NoBind m) [] a)                 = runInferType (Ind Zero (Bind Nothing $ NoBind $ bumpUp m) [] a)

runInferType (Ind Zero (Bind x (NoBind m)) [] a)        = do
  (_, bctx, _) <- ask

  mt <- local (addToBoundCtx (x, Zero)) (runInferType m)
  at <- runCheckType a Zero

  case mt of
    Univ _ -> return $ bumpDown $ open (bumpUp a) m
    _      -> typeError TypeMismatch (Just (showTermWithContext bctx m ++ " is not a term of a universe"))

runInferType (Ind One (NoBind m) [NoBind c] a)          = runInferType (Ind One (Bind Nothing $ NoBind $ bumpUp m) [NoBind c] a)

runInferType (Ind One (Bind x (NoBind m)) [NoBind c] a) = do
  (_, bctx, _) <- ask

  mt <- local (addToBoundCtx (x, One)) (runInferType m)
  ct <- runCheckType c (bumpDown $ open Star m)
  at <- runCheckType a One

  case mt of
    Univ _ -> return $ bumpDown $ open (bumpUp a) m
    _      -> typeError TypeMismatch (Just (showTermWithContext bctx m ++ " is not a term of a universe"))

runInferType (Ind
  (Sigma (x, t) n)
  (NoBind m)
  [Bind w (Bind y (NoBind f))]
  a)                                                    = runInferType (Ind (Sigma (x, t) n) (Bind Nothing $ NoBind $ bumpUp m) [Bind w $ Bind y $ NoBind f] a)

runInferType (Ind
  (Sigma (x, t) n)
  (Bind z (NoBind m))
  [Bind w (Bind y (NoBind f))]
  a)                                                    = do
  (_, bctx, _) <- ask

  mt <- local (addToBoundCtx (z, Sigma (x, t) n)) (runInferType m)
  ft <- local (addToBoundCtx (y, n) . addToBoundCtx (w, t)) (runCheckType f $ openFor (Pair (Var $ Bound 1) (Var $ Bound 0)) 1 (bumpUp m))
  at <- runCheckType a (Sigma (x, t) n)

  case mt of
    Univ _ -> return $ bumpDown $ open (bumpUp a) m
    _      -> typeError TypeMismatch (Just (showTermWithContext bctx m ++ " is not a term of a universe"))

runInferType (Ind
  (Sum t n)
  (NoBind m)
  [Bind x (NoBind c), Bind y (NoBind d)]
  a)                                                    = runInferType (Ind (Sum t n) (Bind Nothing $ NoBind $ bumpUp m) [Bind x $ NoBind c, Bind y $ NoBind d] a)

runInferType (Ind
  (Sum t n)
  (Bind z (NoBind m))
  [Bind x (NoBind c), Bind y (NoBind d)]
  a)                                                    = do
  (_, bctx, _) <- ask

  mt <- local (addToBoundCtx (z , Sum t n)) (runInferType m)
  ct <- local (addToBoundCtx (x, t)) (runCheckType c $ open (bumpUp $ Inl $ Var $ Bound 0) m)
  dt <- local (addToBoundCtx (y, n)) (runCheckType d $ open (bumpUp $ Inr $ Var $ Bound 0) m)
  at <- runCheckType a (Sum t n)

  case mt of
    Univ _ -> return $ bumpDown $ open (bumpUp a) m
    _      -> typeError TypeMismatch (Just (showTermWithContext bctx m ++ " is not a term of a universe"))

runInferType (Ind
  (IdFam t)
  (NoBind m)
  [Bind z (NoBind c), NoBind a, NoBind b]
  p)                                                    = runInferType (Ind (IdFam t) (Bind Nothing $ Bind Nothing $ Bind Nothing $ NoBind $ bumpUp $ bumpUp $ bumpUp m) [Bind z $ NoBind c, NoBind a, NoBind b] p)

runInferType (Ind
  (IdFam t)
  (Bind x (Bind y (Bind p (NoBind m))))
  [Bind z (NoBind c), NoBind a, NoBind b]
  p')                                                   = do
  (_, bctx, _) <- ask

  at <- runInferType a
  bt <- runCheckType b at

  mt  <- local (addToBoundCtx (p, Id (Just $ shift 2 at) (Var $ Bound 2) (Var $ Bound 1)) . addToBoundCtx (y, bumpUp at) . addToBoundCtx (x, at)) (runInferType m)
  ct  <- local (addToBoundCtx (z, at)) (runCheckType c $ openFor (Var $ Bound 0) 2 $ openFor (Var $ Bound 0) 1 $ open (Refl $ Var $ Bound 0) m)
  p't <- runCheckType p' (Id (Just at) a b)

  case mt of
    Univ _ -> return $ openFor a 2 $ openFor b 1 $ open p' m
    _      -> typeError TypeMismatch (Just (showTermWithContext bctx m ++ " is not a term of a universe"))

runInferType (Ind (Var (Free x)) m c a)                 = do
  (env, _, _) <- ask

  case lookup x env of
    Just t  -> runInferType $ Ind t m c a
    Nothing -> typeError FailedToInferType (Just ("Unknown variable " ++ show x))

runInferType (Ind t m c a)                              = typeError FailedToInferType (Just ("Invalid induction " ++ show (Ind t m c a)))

runCheckType :: Term -> Term -> TypeCheck Term
runCheckType m (Var (Free x))                    = do
  (env, bctx, _) <- ask

  case lookup x env of
    Just t  -> do
      t' <- runCheckType m t
      return $ Var $ Free x

    Nothing -> checkInferredTypeMatch m (Var $ Free x)

runCheckType (Lam (x, Just t) m) (Pi (x', t') n) = do
  (_, bctx, _) <- ask

  tt  <- runInferType t
  t't <- runInferType t'
  mt  <- local (addToBoundCtx (Just x, t)) (runCheckType m n)

  case (tt, t't) of
    (Univ i, Univ j) -> if i == j
      then return $ Pi (x', t) mt
      else typeError TypeMismatch (Just ("The type of " ++ showTermWithContext bctx t ++ " is " ++ show (Univ i) ++ " but expected " ++ show (Univ j)))
    (Univ _, _)      -> typeError TypeMismatch (Just (showTermWithContext bctx t' ++ " is not a term of a universe"))
    (_, _)           -> typeError TypeMismatch (Just (showTermWithContext bctx t ++ " is not a term of a universe"))

runCheckType (Lam (x, Nothing) m) (Pi (x', t) n) = do
  (_, bctx, _) <- ask

  tt <- runInferType t
  mt <- local (addToBoundCtx (Just x, t)) (runCheckType m n)

  case tt of
    Univ _ -> return $ Pi (x', t) mt
    _      -> typeError TypeMismatch (Just (showTermWithContext bctx t ++ " is not a term of a universe"))

runCheckType (Pair m n) (Sigma (x, t) t')        = do
  (_, bctx, _) <- ask

  tt  <- runInferType t
  t't <- local (addToBoundCtx (x, t)) (runInferType t')
  mt  <- runCheckType m t
  nt  <- runCheckType n (bumpDown $ open (bumpUp m) t')

  case (tt, t't) of
    (Univ _, Univ _) -> return $ Sigma (x, t) t'
    (Univ _, _)      -> typeError TypeMismatch (Just (showTermWithContext bctx t' ++ " is not a term of a universe: " ++ showTermWithContext bctx t't))
    (_, _)           -> typeError TypeMismatch (Just (showTermWithContext bctx t ++ " is not a term of a universe"))

runCheckType (Inl m) (Sum t t')                  = do
  (env, bctx, _) <- ask

  mt  <- runCheckType m t
  tt  <- runInferType t
  t't <- runInferType t'

  case (tt, t't) of
    (Univ _, Univ _) -> return $ Sum t t'
    (Univ _, _)      -> typeError TypeMismatch (Just (showTermWithContext bctx t' ++ " is not a term of a universe: " ++ showTermWithContext bctx t't))
    (_, _)           -> typeError TypeMismatch (Just (showTermWithContext bctx t ++ " is not a term of a universe"))

runCheckType (Inr m) (Sum t t')                  = do
  (env, bctx, _) <- ask

  mt  <- runCheckType m t'
  tt  <- runInferType t
  t't <- runInferType t'

  case (tt, t't) of
    (Univ _, Univ _) -> return $ Sum t t'
    (Univ _, _)      -> typeError TypeMismatch (Just (showTermWithContext bctx t' ++ " is not a term of a universe: " ++ showTermWithContext bctx t't))
    (_, _)           -> typeError TypeMismatch (Just (showTermWithContext bctx t ++ " is not a term of a universe"))

-- TODO: Check type for inner terms (e.g. reflexivity in a sigma pair)
runCheckType m t                                 = checkInferredTypeMatch m t

checkInferredTypeMatch :: Term -> Term -> TypeCheck Term
checkInferredTypeMatch m t = do
  (env, bctx, _) <- ask

  t'  <- runInferType m
  let et' = eval $ elaborate env t'

  if equal env t et'
  then return t
  else typeError TypeMismatch (Just ("The type of " ++ showTermWithContext bctx m ++ " is " ++ showTermWithContext bctx et' ++ " but expected " ++ showTermWithContext bctx t))

-- Returns True if there is a variable bound to a 0 index binder
-- in the given term
isBinderUsed :: Term -> Bool
isBinderUsed = go 0
  where
    go :: Int -> Term -> Bool
    go k (Var (Bound i))
      | i == k    = True
      | otherwise = False
    go k (Lam (x, Just t) n)  = go k t || go (k + 1) n
    go k (Lam (x, Nothing) n) = go (k + 1) n
    go k (Pi (x, t) n)        = go k t || go (k + 1) n
    go k (Sigma (x, t) n)     = go k t || go (k + 1) n
    go k (Pair t n)           = go k t || go k n
    go k (App t n)            = go k t || go k n
    go k (Id mt m n)          = maybe False (go k) mt || go k m || go k n
    go k (Refl m)             = go k m
    go k (Ind t m' c a)       = go k t || isBinderUsedInBoundTerm k m' || any (isBinderUsedInBoundTerm k) c || go k a
    go k n                    = False

    isBinderUsedInBoundTerm :: Int -> BoundTerm -> Bool
    isBinderUsedInBoundTerm k (NoBind n) = go k n
    isBinderUsedInBoundTerm k (Bind x n) = isBinderUsedInBoundTerm (k + 1) n

showTermWithContext :: BoundContext -> Term -> String
showTermWithContext bctx = showTermWithBinders (map fst bctx)

addToBoundCtx :: (Maybe ByteString, Term) -> ((a, BoundContext, b) -> (a, BoundContext, b))
addToBoundCtx (x, t) (a, bs, b) = (a, (x, bumpUp t) : map (second bumpUp) bs, b)

typeError :: ErrorCode -> Maybe String -> TypeCheck a
typeError errc ms = lift $ Error errc ms
