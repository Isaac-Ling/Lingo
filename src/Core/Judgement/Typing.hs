module Core.Judgement.Typing (inferType, checkType) where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation

import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString)

-- This context records the type of bound variables, where the ith type in the
-- context is the type of the ith binder away from the current term
type BoundContext = [Term]

type TypeCheck a = ReaderT (Environment, BoundContext, Context) CanError a

inferType :: Environment -> Context -> Term -> CanError Term
inferType env ctx m = runReaderT (runInferType m) (env, [], ctx)

checkType :: Environment-> Context -> Term -> Term -> CanError Term
checkType env ctx m t = runReaderT (runCheckType m t) (env, [], ctx)

runInferType :: Term -> TypeCheck Term
runInferType (Univ i)                                                                  = return $ Univ (i + 1)
runInferType Star                                                                      = return One
runInferType Zero                                                                      = return $ Univ 0
runInferType One                                                                       = return $ Univ 0

runInferType (Var (Bound i))                                                           = do
  (_, bctx, _) <- ask

  if i >= 0 && i < length bctx
  then return $ bctx !! i
  else typeError FailedToInferType (Just ("Invalid index for bound term \"" ++ show i ++ "\""))

runInferType (Var (Free x))                                                            = do
  (_, _, ctx) <- ask

  case lookup x ctx of
    Just t  -> return t
    Nothing -> typeError FailedToInferType (Just ("Unknown variable " ++ show x))

runInferType (Pi (x, t) m)                                                             = do
  tt <- runInferType t
  mt <- local (addToBoundCtx tt) (runInferType m)

  case (tt, mt) of
    (Univ i, Univ j) -> return $ Univ $ max i j
    (Univ i, _)      -> typeError TypeMismatch (Just (show m ++ " is not a term of a universe"))
    (_, _)           -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

runInferType (Sigma (x, t) m)                                                          = do
  tt <- runInferType t
  mt <- local (addToBoundCtx t) (runInferType m)

  case (tt, mt) of
    (Univ i, Univ j) -> return $ Univ $ max i j
    (Univ i, _)      -> typeError TypeMismatch (Just (show m ++ " is not a term of a universe"))
    (_, _)           -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

runInferType (Lam (x, Just t) m)                                                       = do
  tt <- runInferType t
  mt <- local (addToBoundCtx t) (runInferType m)

  case tt of
    Univ i -> return $ Pi (if isBinderUsed mt then Just x else Nothing, t) mt
    _      -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

runInferType (Lam (x, Nothing) m) = typeError FailedToInferType (Just ("Cannot infer type of implicit lambda " ++ show (Lam (x, Nothing) m)))

runInferType (App m n)                                                                 = do
  (env, _, _) <- ask

  mt <- runInferType m
  nt <- runInferType n

  case mt of
    Pi (x, t) t' -> if resolve env nt == resolve env t
      then return $ shift (-1) $ open (bumpUp n) t'
      else typeError TypeMismatch (Just (show m ++ " cannot be applied to a term of type " ++ show nt))
    _            -> typeError TypeMismatch (Just (show m ++ " is not a term of a Pi type") )

runInferType (Pair m n)                                                                = do
  mt <- runInferType m
  nt <- runInferType n

  return $ Sigma (Nothing, mt) nt

runInferType (Ind Zero (NoBind m) [] a) = runInferType (Ind Zero (Bind Nothing (NoBind $ bumpUp m)) [] a)

runInferType (Ind Zero (Bind x (NoBind m)) [] a)                                       = do
  mt <- local (addToBoundCtx Zero) (runInferType m)
  at <- runCheckType a Zero

  case mt of
    Univ _ -> return $ bumpDown $ open a m
    _      -> typeError TypeMismatch (Just (show m ++ " is not a term of a universe"))

runInferType (Ind One (NoBind m) [NoBind c] a)                                         = runInferType (Ind One (Bind Nothing (NoBind $ bumpUp m)) [NoBind c] a)

runInferType (Ind One (Bind x (NoBind m)) [NoBind c] a)                                = do
  mt <- local (addToBoundCtx One) (runInferType m)
  ct <- runCheckType c $ bumpDown (open Star m)
  at <- runCheckType a One

  case mt of
    Univ _ -> return $ bumpDown $ open a m
    _      -> typeError TypeMismatch (Just (show m ++ " is not a term of a universe"))

runInferType (Ind (Sigma (x, t) n) (NoBind m) [Bind w (Bind y (NoBind f))] a)          = runInferType (Ind (Sigma (x, t) n) (Bind Nothing (NoBind $ bumpUp m)) [Bind w (Bind y (NoBind f))] a)

runInferType (Ind (Sigma (x, t) n) (Bind z (NoBind m)) [Bind w (Bind y (NoBind f))] a) = do
  mt <- local (addToBoundCtx $ Sigma (x, t) n) (runInferType m)
  ft <- local (addToBoundCtx n . addToBoundCtx t) (runCheckType f $ openFor (Pair (Var $ Bound 1) (Var $ Bound 0)) 1 (bumpUp m))
  at <- runCheckType a (Sigma (x, t) n)

  case mt of
    Univ _ -> return $ bumpDown $ open (bumpUp a) m
    _      -> typeError TypeMismatch (Just (show m ++ " is not a term of a universe"))

runInferType (Ind t m c a)                                                             = typeError FailedToInferType (Just ("Invalid induction " ++ show (Ind t m c a)))

runCheckType :: Term -> Term -> TypeCheck Term
runCheckType (Lam (x, Just t) m) (Pi (x', t') n) = do
  tt  <- runInferType t
  t't <- runInferType t'
  mt  <- local (addToBoundCtx t) (runCheckType m n)

  case (tt, t't) of
    (Univ i, Univ j) -> if i == j
      then return $ Pi (x', t) mt
      else typeError TypeMismatch (Just ("The type of " ++ show t ++ " is " ++ show (Univ i) ++ " but expected " ++ show (Univ j)))
    (Univ _, _)      -> typeError TypeMismatch (Just (show t' ++ " is not a term of a universe"))
    (_, _)           -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

runCheckType (Lam (x, Nothing) m) (Pi (x', t) n) = do
  tt <- runInferType t
  mt <- local (addToBoundCtx t) (runCheckType m n)

  case tt of
    Univ _ -> return $ Pi (x', t) mt
    _      -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

runCheckType (Pair m n) (Sigma (x, t) t') = do
  tt  <- runInferType t
  t't <- local (addToBoundCtx t) (runInferType t')
  mt  <- runCheckType m t
  nt  <- runCheckType n (bumpDown $ open (bumpUp m) t')

  case (tt, t't) of
    (Univ _, Univ _) -> return $ Sigma (x, t) t'
    (Univ _, _)      -> typeError TypeMismatch (Just (show t' ++ " is not a term of a universe: " ++ show t't))
    (_, _)           -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

runCheckType m t                                 = checkInferredTypeMatch m t

checkInferredTypeMatch :: Term -> Term -> TypeCheck Term
checkInferredTypeMatch m t = do
  (env, _, _) <- ask

  t' <- runInferType m

  if resolve env t == resolve env t'
  then return t
  else typeError TypeMismatch (Just ("The type of " ++ show m ++ " is " ++ show t' ++ " but expected " ++ show t))

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
    go k (Ind t m' c a)       = go k t || isBinderUsedInBoundTerm k m' || any (isBinderUsedInBoundTerm k) c || go k a
    go k n                    = False

    isBinderUsedInBoundTerm :: Int -> BoundTerm -> Bool
    isBinderUsedInBoundTerm k (NoBind n) = go k n
    isBinderUsedInBoundTerm k (Bind x n) = isBinderUsedInBoundTerm (k + 1) n

addToBoundCtx :: Term -> ((a, BoundContext, b) -> (a, BoundContext, b))
addToBoundCtx t (a, bs, b) = (a, bumpUp t : map bumpUp bs, b)

typeError :: ErrorCode -> Maybe String -> TypeCheck a
typeError errc ms = lift $ Error errc ms
