module Core.Judgement.Typing where

import Core.Term
import Core.Error
import Core.Judgement.Utils

import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString)

-- This context records the type of bound variables, where the ith type in the
-- context is the type of the ith binder away from the current term
type BoundContext = [Term]

type TypeCheck a = ReaderT (BoundContext, Context) CanError a

inferType :: Context -> Term -> CanError Term
inferType ctx m = runReaderT (runInferType m) ([], ctx)
  where
    runInferType :: Term -> TypeCheck Term
    runInferType (Univ i)             = return $ Univ (i + 1)
    runInferType Star                 = return One
    runInferType Zero                 = return $ Univ 0
    runInferType One                  = return $ Univ 0

    runInferType (Var (Bound i))      = do
      (bctx, _) <- ask

      if i >= 0 && i < length bctx
      then return $ bctx !! i
      else typeError FailedToInferType (Just ("Invalid index for bound term \"" ++ show i ++ "\""))

    runInferType (Var (Free x))      = do
      (_, ctx) <- ask

      case lookup x ctx of
        Just t  -> return t
        Nothing -> typeError FailedToInferType (Just ("Unknown variable " ++ show x))

    runInferType (Pi (x, t) m)       = do
      tt <- runInferType t
      mt <- local (addToBoundCtx tt) (runInferType m)

      case (tt, mt) of
        (Univ i, Univ j) -> return $ Univ $ max i j
        (Univ i, _)      -> typeError TypeMismatch (Just (show m ++ " is not a term of a universe"))
        (_, _)           -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

    runInferType (Sigma (x, t) m)    = do
      tt <- runInferType t
      mt <- local (addToBoundCtx t) (runInferType m)

      case (tt, mt) of
        (Univ i, Univ j) -> return $ Univ $ max i j
        (Univ i, _)      -> typeError TypeMismatch (Just (show m ++ " is not a term of a universe"))
        (_, _)           -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

    runInferType (Lam (x, Just t) m) = do
      tt <- runInferType t
      mt <- local (addToBoundCtx t) (runInferType m)

      case tt of
        Univ i -> return $ Pi (if isBinderUsed mt then Just x else Nothing, t) mt
        _      -> typeError TypeMismatch (Just (show t ++ " is not a term of a universe"))

    runInferType (App m n) = do
      mt <- runInferType m
      nt <- runInferType n

      case mt of
        Pi (x, t) t' -> if nt == t
          then return $ shift (-1) $ open (bump n) t'
          else typeError TypeMismatch (Just (show m ++ " cannot be applied to a term of type " ++ show nt))
        _            -> typeError TypeMismatch (Just (show m ++ " is not a term of a Pi type") )

    runInferType m                   = return m

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

checkType :: Context -> Term -> Term -> CanError Term
checkType ctx m t = runReaderT (runCheckType m t) ([], ctx)
  where
    runCheckType :: Term -> Term -> TypeCheck Term
    runCheckType m = return

addToBoundCtx :: Term -> ((BoundContext, a) -> (BoundContext, a))
addToBoundCtx t (bs, a) = (bump t : map bump bs, a)

typeError :: ErrorCode -> Maybe String -> TypeCheck a
typeError errc ms = lift $ Error errc ms
