module Core.Judgement.Utils where

import Core.Term
import Core.Judgement.Context

import Data.Set (Set)
import Data.ByteString.Lazy.Char8 (ByteString, pack, unpack)
import qualified Data.Set as Set

delta  :: Environment -> Term -> Term
delta env (Var (Free x)) = case lookup x env of
  Just m  -> m
  Nothing -> Var $ Free x
delta _ m                = m

unfold :: Environment -> Term -> Term
unfold env (Var (Free x))           = case lookup x env of
  Just m  -> unfold env m
  Nothing -> Var $ Free x
unfold env (Var (Meta i))           = Var $ Meta i
unfold env (Var (Bound i))          = Var $ Bound i
unfold env (Lam (x, Nothing, ex) m) = Lam (x, Nothing, ex) (unfold env m)
unfold env (Lam (x, Just t, ex) m)  = Lam (x, Just $ unfold env t, ex) (unfold env m)
unfold env (Pi (x, t, ex) m)        = Pi (x, unfold env t, ex) (unfold env m)
unfold env (Sigma (x, t) m)         = Sigma (x, unfold env t) (unfold env m)
unfold env (App m (n, ex))          = App (unfold env m) (unfold env n, ex)
unfold env (Pair m n)               = Pair (unfold env m) (unfold env n)
unfold env (Sum m n)                = Sum (unfold env m) (unfold env n)
unfold env (Inl m)                  = Inl $ unfold env m
unfold env (Inr m)                  = Inr $ unfold env m
unfold env (Refl m)                 = Refl $ fmap (unfold env) m
unfold env (Succ m)                 = Succ $ unfold env m
unfold env (IdFam t)                = IdFam $ unfold env t
unfold env (Funext p)               = Funext $ unfold env p
unfold env (Univalence a)           = Univalence $ unfold env a
unfold env (Id mt m n)              = Id (fmap (unfold env) mt) (unfold env m) (unfold env n)
unfold env (Ind t m c a)            = Ind (unfold env t) (unfoldBoundTerm env m) (map (unfoldBoundTerm env) c) (unfold env a)
  where
    unfoldBoundTerm :: Environment -> BoundTerm -> BoundTerm
    unfoldBoundTerm env (NoBind m) = NoBind $ unfold env m
    unfoldBoundTerm env (Bind x m) = Bind x $ unfoldBoundTerm env m
unfold env m                        = m

shift :: Int -> Term -> Term
shift 0 = id
shift k = go k 0
  where
    -- Second Int is the minimum index that should be shifted
    -- This is used to only shift 'dangling' indices and not
    -- ones that are bound in the given term
    go :: Int -> Int -> Term -> Term
    go k l (Var (Bound i))
      | i >= l    = Var $ Bound (i + k)
      | otherwise = Var $ Bound i
    go k l (Lam (x, Nothing, ex) m) = Lam (x, Nothing, ex) (go k (l + 1) m)
    go k l (Lam (x, Just t, ex) m)  = Lam (x, Just $ go k l t, ex) (go k (l + 1) m)
    go k l (Pi (x, t, ex) m)        = Pi (x, go k l t, ex) (go k (l + 1) m)
    go k l (Sigma (x, t) m)         = Sigma (x, go k l t) (go k (l + 1) m)
    go k l (App m (n, ex))          = App (go k l m) (go k l n, ex)
    go k l (Pair m n)               = Pair (go k l m) (go k l n)
    go k l (Sum m n)                = Sum (go k l m) (go k l n)
    go k l (IdFam t)                = IdFam (go k l t)
    go k l (Id mt m n)              = Id (fmap (go k l) mt) (go k l m) (go k l n)
    go k l (Inl m)                  = Inl $ go k l m
    go k l (Inr m)                  = Inr $ go k l m
    go k l (Succ m)                 = Succ $ go k l m
    go k l (Refl m)                 = Refl $ fmap (go k l) m
    go k l (Funext p)               = Funext $ go k l p
    go k l (Univalence a)           = Funext $ go k l a
    go k l (Ind t m c a)            = Ind (go k l t) (shiftInBoundTerm k l m) (map (shiftInBoundTerm k l) c) (go k l a)
    go k l m                        = m

    shiftInBoundTerm :: Int -> Int -> BoundTerm -> BoundTerm
    shiftInBoundTerm k l (NoBind m) = NoBind $ go k l m
    shiftInBoundTerm k l (Bind a m) = Bind a $ shiftInBoundTerm k (l + 1) m

bumpUp :: Term -> Term
bumpUp = shift 1

bumpDown :: Term -> Term
bumpDown = shift (-1)

-- Opening a term with another term refers to substituting the former term for bound variables
-- of index 0 in the latter term
open :: Term -> Term -> Term
open m = openFor m 0

openFor :: Term -> Int -> Term -> Term
openFor m k (Var (Bound i))
  | i == k    = m
  | otherwise = Var $ Bound i
openFor m k (Lam (x, Just t, ex) n)  = Lam (x, Just $ openFor m k t, ex) (openFor (bumpUp m) (k + 1) n)
openFor m k (Lam (x, Nothing, ex) n) = Lam (x, Nothing, ex) (openFor (bumpUp m) (k + 1) n)
openFor m k (Pi (x, t, ex) n)        = Pi (x, openFor m k t, ex) (openFor (bumpUp m) (k + 1) n)
openFor m k (Sigma (x, t) n)         = Sigma (x, openFor m k t) (openFor (bumpUp m) (k + 1) n)
openFor m k (Pair t n)               = Pair (openFor m k t) (openFor m k n)
openFor m k (IdFam t)                = IdFam $ openFor m k t
openFor m k (Id mt t n)              = Id (fmap (openFor m k) mt) (openFor m k t) (openFor m k n)
openFor m k (Sum t n)                = Sum (openFor m k t) (openFor m k n)
openFor m k (App t (n, ex))          = App (openFor m k t) (openFor m k n, ex)
openFor m k (Inl n)                  = Inl $ openFor m k n
openFor m k (Inr n)                  = Inr $ openFor m k n
openFor m k (Refl n)                 = Refl $ fmap (openFor m k) n
openFor m k (Succ n)                 = Succ $ openFor m k n
openFor m k (Funext p)               = Funext $ openFor m k p
openFor m k (Univalence a)           = Univalence $ openFor m k a
openFor m k (Ind t m' c a)           = Ind (openFor m k t) (openInBoundTerm m k m') (map (openInBoundTerm m k) c) (openFor m k a)
  where
    openInBoundTerm :: Term -> Int -> BoundTerm -> BoundTerm
    openInBoundTerm m k (NoBind n) = NoBind (openFor m k n)
    openInBoundTerm m k (Bind x n) = Bind x (openInBoundTerm (bumpUp m) (k + 1) n)
openFor m k n                        = n

-- Returns True if there is a variable bound to a 0 index binder in the given term
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
    go k (Sum m n)               = go k m || go k n
    go k (Pair t n)              = go k t || go k n
    go k (App t (n, _))          = go k t || go k n
    go k (Id mt m n)             = maybe False (go k) mt || go k m || go k n
    go k (Refl m)                = maybe False (go k) m
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

getMetasInTerm :: Term -> Set Int
getMetasInTerm (Var (Meta i))          = Set.singleton i
getMetasInTerm (Lam (x, Just t, _) n)  = getMetasInTerm t <> getMetasInTerm n
getMetasInTerm (Lam (x, Nothing, _) n) = getMetasInTerm n
getMetasInTerm (Pi (x, t, _) n)        = getMetasInTerm t <> getMetasInTerm n
getMetasInTerm (Sum m n)               = getMetasInTerm m <> getMetasInTerm n
getMetasInTerm (Sigma (x, t) n)        = getMetasInTerm t <> getMetasInTerm n
getMetasInTerm (Pair t n)              = getMetasInTerm t <> getMetasInTerm n
getMetasInTerm (App t (n, _))          = getMetasInTerm t <> getMetasInTerm n
getMetasInTerm (Id mt m n)             = maybe Set.empty getMetasInTerm mt <> getMetasInTerm m <> getMetasInTerm n
getMetasInTerm (Refl m)                = maybe Set.empty getMetasInTerm m
getMetasInTerm (Funext m)              = getMetasInTerm m
getMetasInTerm (Univalence m)          = getMetasInTerm m
getMetasInTerm (Succ m)                = getMetasInTerm m
getMetasInTerm (Inl m)                 = getMetasInTerm m
getMetasInTerm (Inr m)                 = getMetasInTerm m
getMetasInTerm (IdFam m)               = getMetasInTerm m
getMetasInTerm (Ind t m' c a)          = getMetasInTerm t <> getMetasInBoundTerm m' <> Set.unions (map getMetasInBoundTerm c) <> getMetasInTerm a
  where
    getMetasInBoundTerm :: BoundTerm -> Set Int
    getMetasInBoundTerm (NoBind m) = getMetasInTerm m
    getMetasInBoundTerm (Bind _ m) = getMetasInBoundTerm m
getMetasInTerm m                       = Set.empty

containsMeta :: Term -> Bool
containsMeta = not . Set.null . getMetasInTerm

getUnivVarsInTerm :: Term -> Set Int
getUnivVarsInTerm (Univ (UVar i))         = Set.singleton i
getUnivVarsInTerm (Lam (x, Just t, _) n)  = getUnivVarsInTerm t <> getUnivVarsInTerm n
getUnivVarsInTerm (Lam (x, Nothing, _) n) = getUnivVarsInTerm n
getUnivVarsInTerm (Pi (x, t, _) n)        = getUnivVarsInTerm t <> getUnivVarsInTerm n
getUnivVarsInTerm (Sum m n)               = getUnivVarsInTerm m <> getUnivVarsInTerm n
getUnivVarsInTerm (Sigma (x, t) n)        = getUnivVarsInTerm t <> getUnivVarsInTerm n
getUnivVarsInTerm (Pair t n)              = getUnivVarsInTerm t <> getUnivVarsInTerm n
getUnivVarsInTerm (App t (n, _))          = getUnivVarsInTerm t <> getUnivVarsInTerm n
getUnivVarsInTerm (Id mt m n)             = maybe Set.empty getUnivVarsInTerm mt <> getUnivVarsInTerm m <> getUnivVarsInTerm n
getUnivVarsInTerm (Refl m)                = maybe Set.empty getUnivVarsInTerm m
getUnivVarsInTerm (Funext m)              = getUnivVarsInTerm m
getUnivVarsInTerm (Univalence m)          = getUnivVarsInTerm m
getUnivVarsInTerm (Succ m)                = getUnivVarsInTerm m
getUnivVarsInTerm (Inl m)                 = getUnivVarsInTerm m
getUnivVarsInTerm (Inr m)                 = getUnivVarsInTerm m
getUnivVarsInTerm (IdFam m)               = getUnivVarsInTerm m
getUnivVarsInTerm (Ind t m' c a)          = getUnivVarsInTerm t <> getMetasInBoundTerm m' <> Set.unions (map getMetasInBoundTerm c) <> getUnivVarsInTerm a
  where
    getMetasInBoundTerm :: BoundTerm -> Set Int
    getMetasInBoundTerm (NoBind m) = getUnivVarsInTerm m
    getMetasInBoundTerm (Bind _ m) = getMetasInBoundTerm m
getUnivVarsInTerm m                       = Set.empty

containsUnivVar :: Term -> Bool
containsUnivVar = not . Set.null . getUnivVarsInTerm

isRigid :: Term -> Bool
isRigid (Var (Meta _)) = False
isRigid (App m _)      = isRigid m
isRigid _              = True

isFlex :: Term -> Bool
isFlex = not . isRigid
