module Core.Judgement.Evaluation where

import Core.Term
import Core.Error
import Core.Judgement.Utils

import Data.ByteString.Lazy.Char8 (ByteString)

eval :: Term -> Term
eval (Lam _ (App f (Var (Bound 0))))                             = eval f -- Eta conversion
eval (Lam (x, Just t) m)                                         = Lam (x, Just $ eval t) (eval m)
eval (Lam (x, Nothing) m)                                        = Lam (x, Nothing) (eval m)
eval (Pi (x, t) m)                                               = Pi (x, eval t) (eval m)
eval (Sigma (x, t) m)                                            = Sigma (x, eval t) (eval m)
eval (App m n)
  | isNeutral f = App f (eval n)
  | otherwise   = eval (beta (App f n))
  where
    f :: Term
    f = eval m
eval (Ind One _ [NoBind c] _)                                    = c
eval (Ind (Sigma _ _) _ [Bind w (Bind y (NoBind f))] (Pair a b)) = eval (App (App (Lam (w, Nothing) $ Lam (y, Nothing) f) a) b)
eval m                                                           = m

isValue :: Term -> Bool
isValue (Lam _ _) = True
isValue (Var x)   = True
isValue m         = isNeutral m

isNeutral :: Term -> Bool
isNeutral (Var x)   = True
isNeutral (App m n) = isNeutral m && isValue n
isNeutral Star      = True
isNeutral (Univ _)  = True
isNeutral Zero      = True
isNeutral One       = True
isNeutral _         = False

beta :: Term -> Term
beta (App (Lam _ m) n) = open n m
beta m                 = m

-- Opening a term with another term refers to substituting the latter term for bound variables
-- of index 0 in the former term
open :: Term -> Term -> Term
open m = go m 0
  where
    go :: Term -> Int -> Term -> Term
    go m k (Var (Bound i))
      | i == k    = m
      | otherwise = Var $ Bound i
    go m k (Lam (x, Just t) n)  = Lam (x, Just $ go m k t) (go m (k + 1) n)
    go m k (Lam (x, Nothing) n) = Lam (x, Nothing) (go m (k + 1) n)
    go m k (Pi (x, t) n)        = Pi (x, go m k t) (go m (k + 1) n)
    go m k (Sigma (x, t) n)     = Sigma (x, go m k t) (go m (k + 1) n)
    go m k (Pair t n)           = Pair (go m k t) (go m k n)
    go m k (App t n)            = App (go m k t) (go m k n)
    go m k (Ind t m' c a)       = Ind (go m k t) (openInBoundTerm m k m') (map (openInBoundTerm m k) c) (go m k a)
    go m k n                    = n

    openInBoundTerm :: Term -> Int -> BoundTerm -> BoundTerm
    openInBoundTerm m k (NoBind n) = NoBind (go m k n)
    openInBoundTerm m k (Bind x n) = Bind x (openInBoundTerm m (k + 1) n)

-- Judgemental equality of terms/types is alpha-beta-eta equivalence
instance JudgementalEq Term where
  (===) m n env = eval (resolve env m) == eval (resolve env n)

instance JudgementalEq BoundTerm where
  (===) m n env = evalBoundTerm (resolveBoundTerm env m) == evalBoundTerm (resolveBoundTerm env n)
    where
      evalBoundTerm :: BoundTerm -> BoundTerm
      evalBoundTerm (NoBind m) = NoBind (eval m)
      evalBoundTerm (Bind x m) = Bind x $ evalBoundTerm m

      resolveBoundTerm :: Environment -> BoundTerm -> BoundTerm
      resolveBoundTerm env (NoBind m) = NoBind (resolve env m)
      resolveBoundTerm env (Bind x m) = Bind x $ resolveBoundTerm env m
