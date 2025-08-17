module Core.Judgement.Typing (inferType, checkType) where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation

import Data.Bifunctor (second)
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.ByteString.Lazy.Char8 (ByteString)

-- This context records the type of bound variables, where the ith type in the
-- context is the type of the ith binder away from the current term
type BoundContext = [(Maybe ByteString, Term)]

data MetaSolution = MetaSolution
  { metaType :: Term
  , metaTerm :: Maybe Term
  }

type MetaContext = [(Int, MetaSolution)]

data Contexts = Contexts
  { env   :: Environment
  , ctx   :: Context
  , bctx  :: BoundContext
  , tbctx :: BoundContext
  }

-- A constraint is an equality of the first term with the second
type Constraint = (Term, Term)
type Constraints = [Constraint]

data TypeState = TypeState
  { csts   :: Constraints
  , mctx   :: MetaContext
  , metaID :: Int
  }

type TypeCheck a = ReaderT Contexts (StateT TypeState CanError) a

inferType :: Environment -> Context -> Term -> CanError Term
inferType env ctx m = evalStateT (runReaderT (runInferType m) initContexts) initState
  where
    initContexts = Contexts { env=env, ctx=ctx, bctx=[], tbctx=[] }
    initState    = TypeState { csts=[], mctx=[], metaID=0 }

checkType :: Environment-> Context -> Term -> Term -> CanError Term
checkType env ctx m t = evalStateT (runReaderT (runCheckType m t) initContexts) initState
  where
    initContexts = Contexts { env=env, ctx=ctx, bctx=[], tbctx=[] }
    initState    = TypeState { csts=[], mctx=[], metaID=0 }

runInferType :: Term -> TypeCheck Term
runInferType (Univ i)                                  = return $ Univ (i + 1)
runInferType Star                                      = return Top
runInferType Bot                                       = return $ Univ 0
runInferType Top                                       = return $ Univ 0
runInferType Nat                                       = return $ Univ 0

runInferType (Var (Bound i))                           = do
  ctxs <- ask

  if i >= 0 && i < length (bctx ctxs)
  then return $ snd $ bctx ctxs !! i
  else typeError FailedToInferType (Just ("Invalid index for bound term \"" ++ show i ++ "\""))

runInferType (Var (Free x))                            = do
  ctxs <- ask

  case lookup x $ ctx ctxs of
    Just t  -> return t
    Nothing -> typeError FailedToInferType (Just ("Unknown variable " ++ show x))

runInferType (Var (Meta i))                            = do
  st <- get

  case lookup i $ mctx st of
    Just t  -> return $ metaType t
    Nothing -> typeError FailedToInferType (Just ("Unknown meta variable " ++ show (Var $ Meta i)))

runInferType (Pi (x, t, _) m)                        = do
  ctxs <- ask

  tt <- runInferType t
  mt <- local (addToBoundCtx (x, t)) (runInferType m)

  case (tt, mt) of
    (Univ i, Univ j) -> return $ Univ $ max i j
    (Univ i, _)      -> typeError TypeMismatch (Just (showTermWithContext ((x, t) : bctx ctxs) m ++ " is not a term of a universe"))
    (_, _)           -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

runInferType (Sigma (x, t) m)                          = do
  ctxs <- ask

  tt <- runInferType t
  mt <- local (addToBoundCtx (x, t)) (runInferType m)

  case (tt, mt) of
    (Univ i, Univ j) -> return $ Univ $ max i j
    (Univ i, _)      -> typeError TypeMismatch (Just (showTermWithContext ((x, t) : bctx ctxs) m ++ " is not a term of a universe"))
    (_, _)           -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

runInferType (Lam (x, Just t, ex) m)                   = do
  ctxs <- ask

  tt <- runInferType t
  mt <- local (addToBoundCtx (Just x, t)) (runInferType m)

  case tt of
    Univ i -> return $ Pi (if isBinderUsed mt then Just x else Nothing, t, ex) mt
    _      -> typeError TypeMismatch (Just (showTermWithContext (bctx ctxs)  t ++ " is not a term of a universe"))

runInferType (Lam (x, Nothing, ex) m)                  = do
  ctxs <- ask

  typeError FailedToInferType (Just ("Cannot infer type of implicit lambda " ++ showTermWithContext (bctx ctxs) (Lam (x, Nothing, ex) m)))

runInferType (App m n)                                 = do
  mt <- runInferType m
  inferAppType m n mt
    where
      inferAppType :: Term -> Term -> Term -> TypeCheck Term
      inferAppType m n mt = do
        ctxs <- ask

        case mt of
          Pi (x, t, Exp) t' -> do
            nt <- runInferType n

            if equal (env ctxs) t nt
            then return $ bumpDown $ open (bumpUp n) t'
            else typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) m ++ " of type " ++ showTermWithContext (bctx ctxs) mt ++ " cannot be applied to " ++ showTermWithContext (bctx ctxs) n ++ " of type " ++ showTermWithContext (bctx ctxs) nt)
          Pi (x, t, Imp) t' -> do
            mv <- createMetaVar t
            let m'  = App m mv
            let m't = bumpDown $ open mv t'

            inferAppType m' n m't
          _                 -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) m ++ " is not a term of a Pi type")

runInferType (Pair m n)                                = do
  mt <- runInferType m
  nt <- runInferType n

  return $ Sigma (Nothing, mt) nt

runInferType (Sum m n)                                 = do
  ctxs <- ask

  mt <- runInferType m
  nt <- runInferType n

  case (mt, nt) of
    (Univ i, Univ j) -> return $ Univ $ max i j
    (Univ i, _)      -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) n ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (show m ++ " is not a term of a universe")

runInferType (Inl m)                                   = do
  ctxs <- ask

  typeError FailedToInferType $ Just ("Cannot infer type of ambiguous injection " ++ showTermWithContext (bctx ctxs) (Inl m))

runInferType (Inr m)                                   = do
  ctxs <- ask

  typeError FailedToInferType $ Just ("Cannot infer type of ambiguous injection " ++ showTermWithContext (bctx ctxs) (Inr m))

runInferType Zero                                      = return Nat

runInferType (Succ m)                                  = do
  ctxs <- ask

  mt <- runInferType m

  case mt of
    Nat -> return Nat
    _   -> typeError FailedToInferType $ Just ("Cannot apply succ to a term of type " ++ showTermWithContext (bctx ctxs) mt)

runInferType (Funext p)                                = do
  ctxs <- ask

  pt <- runInferType p

  case pt of
    Pi _ (Id _ (App f (Var (Bound 0))) (App g (Var (Bound 0)))) -> return $ Id Nothing f g
    _                                                           -> typeError FailedToInferType $ Just ("Cannot apply funext to a term of type " ++ showTermWithContext (bctx ctxs) pt)

-- TODO: Type check univalence
runInferType (Univalence f)                            = do
  ctxs <- ask

  ft <- runInferType f

  case ft of
    Top -> return Top
    _   -> typeError FailedToInferType $ Just ("Cannot apply funext to a term of type " ++ showTermWithContext (bctx ctxs) ft)

runInferType (IdFam t)                                 = do
  ctxs <- ask

  tt <- runInferType t
  case tt of
    Univ i -> return $ Pi (Nothing, t, Exp) $ Pi (Nothing, t, Exp) tt
    _      -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs)t ++ " is not a term of a universe")

runInferType (Id Nothing m n)                          = do
  mt  <- runInferType m
  mtt <- runInferType mt
  nt  <- runCheckEvaluatedType n mt

  return mtt

runInferType (Id (Just t) m n)                         = runCheckEvaluatedType (Id Nothing m n) t

runInferType (Refl m)                                  = return $ Id Nothing m m

runInferType (Ind Bot (NoBind m) [] a)                 = runInferType (Ind Bot (Bind Nothing $ NoBind $ bumpUp m) [] a)

runInferType (Ind Bot (Bind x (NoBind m)) [] a)        = do
  ctxs <- ask

  mt <- local (addToBoundCtx (x, Bot)) (runInferType m)
  at <- runCheckType a Bot

  case mt of
    Univ _ -> return $ bumpDown $ open (bumpUp a) m
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((x, Bot) : bctx ctxs) m ++ " is not a term of a universe")

runInferType (Ind Top (NoBind m) [NoBind c] a)          = runInferType (Ind Top (Bind Nothing $ NoBind $ bumpUp m) [NoBind c] a)

runInferType (Ind Top (Bind x (NoBind m)) [NoBind c] a) = do
  ctxs <- ask

  mt <- local (addToBoundCtx (x, Top)) (runInferType m)
  ct <- runCheckEvaluatedType c (bumpDown $ open Star m)
  at <- runCheckType a Top

  case mt of
    Univ _ -> return $ bumpDown $ open (bumpUp a) m
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((x, Top) : bctx ctxs) m ++ " is not a term of a universe")

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
  ctxs <- ask

  mt <- local (addToBoundCtx (z, Sigma (x, t) n)) (runInferType m)
  ft <- local (addToBoundCtx (y, n) . addToBoundCtx (w, t)) (runCheckEvaluatedType f $ openFor (Pair (Var $ Bound 1) (Var $ Bound 0)) 1 (bumpUp m))
  at <- runCheckEvaluatedType a (Sigma (x, t) n)

  case mt of
    Univ _ -> return $ bumpDown $ open (bumpUp a) m
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((z, Sigma (x, t) n) : bctx ctxs) m ++ " is not a term of a universe")

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
  ctxs <- ask

  mt <- local (addToBoundCtx (z, Sum t n)) (runInferType m)
  ct <- local (addToBoundCtx (x, t)) (runCheckEvaluatedType c $ open (Inl $ Var $ Bound 1) m)
  dt <- local (addToBoundCtx (y, n)) (runCheckEvaluatedType d $ open (Inr $ Var $ Bound 1) m)
  at <- runCheckEvaluatedType a (Sum t n)

  case mt of
    Univ _ -> return $ bumpDown $ open (bumpUp a) m
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((z, Sum t n) : bctx ctxs) m ++ " is not a term of a universe")

runInferType (Ind
  (IdFam t)
  (NoBind m)
  [Bind z (NoBind c), NoBind a, NoBind b]
  p)                                                    = runInferType (Ind (IdFam t) (Bind Nothing $ Bind Nothing $ Bind Nothing $ NoBind $ shift 3 m) [Bind z $ NoBind c, NoBind a, NoBind b] p)

runInferType (Ind
  (IdFam t)
  (NoBind m)
  [Bind z (NoBind c), NoBind a, NoBind b]
  p)                                                    = runInferType (Ind (IdFam t) (Bind Nothing $ Bind Nothing $ Bind Nothing $ NoBind $ shift 3 m) [Bind z $ NoBind c, NoBind a, NoBind b] p)

runInferType (Ind
  (IdFam t)
  (Bind x (Bind y (Bind p (NoBind m))))
  [Bind z (NoBind c), NoBind a, NoBind b]
  p')                                                   = do
  ctxs <- ask

  at <- runCheckEvaluatedType a t
  bt <- runCheckEvaluatedType b t

  mt  <- local (addToBoundCtx (p, Id (Just $ shift 2 t) (Var $ Bound 2) (Var $ Bound 1)) . addToBoundCtx (y, bumpUp t) . addToBoundCtx (x, t)) (runInferType m)
  ct  <- local (addToBoundCtx (z, t)) (runCheckEvaluatedType c $ shift (-2) $ openFor (Var $ Bound 2) 2 $ openFor (Var $ Bound 2) 1 $ open (Refl $ Var $ Bound 2) m)
  p't <- runCheckEvaluatedType p' (Id (Just t) a b)

  case mt of
    Univ _ -> return $ shift (-3) $ openFor (shift 3 a) 2 $ openFor (shift 3 b) 1 $ open (shift 3 p') m
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((p, Id (Just $ shift 2 t) (Var $ Bound 2) (Var $ Bound 1)) : (y, bumpUp t) : (x, t) : bctx ctxs) m ++ " is not a term of a universe")

runInferType (Ind (Var (Free x)) m c a)                 = do
  ctxs <- ask

  case lookup x $ env ctxs of
    Just t  -> runInferType $ Ind t m c a
    Nothing -> typeError FailedToInferType $ Just ("Unknown variable " ++ show x)

runInferType (Ind
  Nat
  (NoBind m)
  [NoBind c0, Bind w (Bind z (NoBind cs))]
  n)                                                    = runInferType (Ind Nat (Bind Nothing $ NoBind $ bumpUp m) [NoBind c0, Bind w (Bind z (NoBind cs))] n)

runInferType (Ind
  Nat
  (Bind x (NoBind m))
  [NoBind c0, Bind w (Bind z (NoBind cs))]
  n)                                                    = do
  ctxs <- ask

  nt  <- runCheckType n Nat
  mt  <- local (addToBoundCtx (x, Nat)) (runInferType m)
  c0t <- runCheckEvaluatedType c0 $ bumpDown $ open Zero m
  cst <- local (addToBoundCtx (z, m) . addToBoundCtx (w, Nat)) (runCheckEvaluatedType cs $ bumpUp $ open (Succ $ Var $ Bound 0) m)

  case mt of
    Univ _ -> return $ bumpDown $ open (bumpUp n) m
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((x, Nat) : bctx ctxs) m ++ " is not a term of a universe")

runInferType (Ind t m c a)                              = typeError FailedToInferType $ Just ("Invalid induction " ++ show (Ind t m c a))

runCheckEvaluatedType :: Term -> Term -> TypeCheck Term
runCheckEvaluatedType m t = do
  ctxs <- ask

  runCheckType m (eval $ resolve (env ctxs) t)

runCheckType :: Term -> Term -> TypeCheck Term
runCheckType m (Var (Free x))                             = do
  ctxs <- ask

  case lookup x $ env ctxs of
    Just t  -> do
      t' <- runCheckType m t
      return $ Var $ Free x
    Nothing -> checkInferredTypeMatch m (Var $ Free x)

runCheckType (Lam (x, Just t, ex) m) (Pi (x', t', ex') n) = do
  ctxs <- ask

  tt  <- runInferType t
  t't <- runInferType t'
  mt  <- local (addToBoundCtxs (Just x, t) (x', t')) (runCheckType m n)

  case (tt, t't, ex == ex') of
    (_, _, False)       -> typeError TypeMismatch $ Just ("Mismatching explicitness between " ++ showTermWithContext (bctx ctxs) (Lam (x, Just t, ex) m) ++ " and " ++ showTermWithContext (tbctx ctxs) (Pi (x', t, ex') n))
    (Univ i, Univ j, _) -> if i == j
      then return $ Pi (x', t, Exp) mt
      else typeError TypeMismatch $ Just ("The type of " ++ showTermWithContext (bctx ctxs) t ++ " is " ++ show (Univ i) ++ " but expected " ++ show (Univ j))
    (Univ _, _, _)      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t' ++ " is not a term of a universe")
    (_, _, _)           -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) t ++ " is not a term of a universe")

runCheckType (Lam (x, Nothing, ex) m) (Pi (x', t, ex') n) = do
  ctxs <- ask

  tt <- runInferType t
  mt <- local (addToBoundCtxs (Just x, t) (x', t)) (runCheckType m n)

  case tt of
    Univ _ -> if ex == ex'
      then return $ Pi (x', t, Exp) mt
      else typeError TypeMismatch $ Just ("Mismatching explicitness between " ++ showTermWithContext (bctx ctxs) (Lam (x, Nothing, ex) m) ++ " and " ++ showTermWithContext (tbctx ctxs) (Pi (x', t, ex') n))
    _      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t ++ " is not a term of a universe")

runCheckType (Pair m n) (Sigma (x, t) t')                 = do
  ctxs <- ask

  tt  <- runInferType t
  t't <- local (useTypeBoundCtx . addToBoundCtx (x, t)) (runInferType t')
  mt  <- runCheckType m t
  nt  <- runCheckType n (bumpDown $ open (bumpUp m) t')

  case (tt, t't) of
    (Univ _, Univ _) -> return $ Sigma (x, t) t'
    (Univ _, _)      -> typeError TypeMismatch $ Just (showTermWithContext ((x, t) : tbctx ctxs) t' ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t ++ " is not a term of a universe")

runCheckType (Inl m) (Sum t t')                           = do
  ctxs <- ask

  mt  <- runCheckType m t
  tt  <- runInferType t
  t't <- runInferType t'

  case (tt, t't) of
    (Univ _, Univ _) -> return $ Sum t t'
    (Univ _, _)      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t' ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t ++ " is not a term of a universe")

runCheckType (Inr m) (Sum t t')                           = do
  ctxs <- ask

  mt  <- runCheckType m t'
  tt  <- runInferType t
  t't <- runInferType t'

  case (tt, t't) of
    (Univ _, Univ _) -> return $ Sum t t'
    (Univ _, _)      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t' ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t ++ " is not a term of a universe")

runCheckType m t                                          = checkInferredTypeMatch m t

checkInferredTypeMatch :: Term -> Term -> TypeCheck Term
checkInferredTypeMatch m t = do
  ctxs <- ask

  t' <- runInferType m

  if equal (env ctxs) t t'
  then return t
  else typeError TypeMismatch $ Just ("The type of " ++ showTermWithContext (bctx ctxs) m ++ " is " ++ showTermWithContext (bctx ctxs) (eval t') ++ " but expected " ++ showTermWithContext (tbctx ctxs) t)

-- Returns True if there is a variable bound to a 0 index binder
-- in the given term
isBinderUsed :: Term -> Bool
isBinderUsed = go 0
  where
    go :: Int -> Term -> Bool
    go k (Var (Bound i))
      | i == k    = True
      | otherwise = False
    go k (Lam (x, Just t, _) n)  = go k t || go (k + 1) n
    go k (Lam (x, Nothing, _) n) = go (k + 1) n
    go k (Pi (x, t, _) n)        = go k t || go (k + 1) n
    go k (Sigma (x, t) n)        = go k t || go (k + 1) n
    go k (Pair t n)              = go k t || go k n
    go k (App t n)               = go k t || go k n
    go k (Id mt m n)             = maybe False (go k) mt || go k m || go k n
    go k (Refl m)                = go k m
    go k (Funext m)              = go k m
    go k (Univalence m)          = go k m
    go k (Succ m)                = go k m
    go k (Inl m)                 = go k m
    go k (Inr m)                 = go k m
    go k (IdFam m)               = go k m
    go k (Ind t m' c a)          = go k t || isBinderUsedInBoundTerm k m' || any (isBinderUsedInBoundTerm k) c || go k a
    go k n                       = False

    isBinderUsedInBoundTerm :: Int -> BoundTerm -> Bool
    isBinderUsedInBoundTerm k (NoBind n) = go k n
    isBinderUsedInBoundTerm k (Bind x n) = isBinderUsedInBoundTerm (k + 1) n

showTermWithContext :: BoundContext -> Term -> String
showTermWithContext bctx = showTermWithBinders (map fst bctx)

addToCtx :: Assumption -> (Contexts -> Contexts)
addToCtx (x, t) ctxs = ctxs { ctx=(x, t) : ctx ctxs }

addToBoundCtx :: (Maybe ByteString, Term) -> (Contexts -> Contexts)
addToBoundCtx (x, t) ctxs = ctxs { bctx=(x, bumpUp t) : map (second bumpUp) (bctx ctxs) }

addToTypeBoundCtx :: (Maybe ByteString, Term) -> (Contexts -> Contexts)
addToTypeBoundCtx (x, t) ctxs = ctxs { tbctx=(x, bumpUp t) : map (second bumpUp) (bctx ctxs) }

addToBoundCtxs :: (Maybe ByteString, Term) -> (Maybe ByteString, Term) -> (Contexts -> Contexts)
addToBoundCtxs (x, t) (x', t') = addToTypeBoundCtx (x', t') . addToBoundCtx (x, t)

useTypeBoundCtx :: Contexts -> Contexts
useTypeBoundCtx ctxs = ctxs { bctx=tbctx ctxs }

createMetaVar :: Term -> TypeCheck Term
createMetaVar mt = do
  st <- get
  let mid = metaID st
  put st { metaID=mid + 1, mctx=(mid, MetaSolution { metaTerm=Nothing, metaType=mt }) : mctx st }

  return $ Var $ Meta mid

typeError :: ErrorCode -> Maybe String -> TypeCheck a
typeError errc ms = lift $ lift $ Error errc ms
