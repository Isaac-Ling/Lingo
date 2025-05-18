module Core.Judgement.Utils where

import Core.Term
import Core.Error

import Data.List (elemIndex)
import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString)

-- This context records the type of bound variables, where the ith type in the
-- context is the type of the ith binder away from the current term
type BoundContext = [Term]

type TypeCheck a = ReaderT (BoundContext, Context) CanError a

-- A list of binders, where the ith element is the ith binder away from the
-- current term. Nothing is used if we should never match against that binder
type Binders = [Maybe ByteString]

toDeBruijn :: NamedTerm -> Term
toDeBruijn = go []
  where
    go :: Binders -> NamedTerm -> Term
    go bs (NVar x)          = case elemIndex (Just x) bs of
      Just i  -> Var (Bound i)
      Nothing -> Var (Free x)
    go bs (NLam (NImp x) m)      = Lam Nothing (go (Just x : bs) m)
    go bs (NLam (NExp (x, t)) m) = Lam (Just (go bs t)) (go (Just x : bs) m)
    go bs (NPi (x, t) m)         = Pi (go bs t) (go (Just x : bs) m)
    go bs (NArr t m)             = Pi (go bs t) (go (Nothing : bs) m)
    go bs (NSigma (x, t) m)      = Sigma (go bs t) (go (Just x : bs) m)
    go bs (NProd t m)            = Sigma (go bs t) (go (Nothing : bs) m)
    go bs (NApp m n)             = App (go bs m) (go bs n)
    go bs (NPair m n)            = Pair (go bs m) (go bs n)
    go bs (NInd t m c a)         = Ind (go bs t) (boundTermToDeBruijn bs m) (map (boundTermToDeBruijn bs) c) (go bs a)
    go bs (NUniv i)              = Univ i
    go bs NZero                  = Zero
    go bs NOne                   = One
    go bs NStar                  = Star

    boundTermToDeBruijn :: Binders -> NamedBoundTerm -> BoundTerm
    boundTermToDeBruijn bs (NNoBind m) = NoBind $ go bs m
    boundTermToDeBruijn bs (NBind x m) = Bind $ boundTermToDeBruijn (Just x : bs) m

resolve :: Environment -> Term -> Term
resolve env (Var (Free x)) = case lookup x env of
  Just m  -> m
  Nothing -> Var $ Free x
resolve env m              = m
