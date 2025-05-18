module Core.Judgement.Evaluation where

import Core.Term
import Core.Error
import Core.Judgement.Utils

import Data.ByteString.Lazy.Char8 (ByteString)

eval :: Term -> Term
eval (Lam _ (App f (Var (Bound 0))))                             = eval f -- Eta conversion
eval (Lam (Just t) m)                                            = Lam (Just $ eval t) (eval m)
eval (Lam Nothing m)                                             = Lam Nothing (eval m)
eval (Pi t m)                                                    = Pi (eval t) (eval m)
eval (Sigma t m)                                                 = Sigma (eval t) (eval m)
eval (App m n)
  | isNeutral f = App f (eval n)
  | otherwise     = eval (beta (App f n))
  where
    f :: Term
    f = eval m
eval (Ind One _ [NoBind c] _)                                    = c
-- TODO: Implement eval for sigma induction
--eval (Ind (Sigma _ _) _ [Bind w (Bind y (NoBind f))] (Pair a b)) = sub e a w (sub e b y f)
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
    go m k (Lam (Just t) n) = Lam (Just $ go m k t) (go m (k + 1) n)
    go m k (Lam Nothing n)  = Lam Nothing (go m (k + 1) n)
    go m k (Pi t n)         = Pi (go m k t) (go m (k + 1) n)
    go m k (Sigma t n)      = Sigma (go m k t) (go m (k + 1) n)
    go m k (Pair t n)       = Pair (go m k t) (go m k n)
    go m k (App t n)        = App (go m k t) (go m k n)
    go m k (Ind t m' c a)   = Ind (go m k t) (openInBoundTerm m k m') (map (openInBoundTerm m k) c) (go m k a)
    go m k n                = n

    openInBoundTerm :: Term -> Int -> BoundTerm -> BoundTerm
    openInBoundTerm m k (NoBind n) = NoBind (go m k n)
    openInBoundTerm m k (Bind n)   = Bind (openInBoundTerm m (k + 1) n)

-- Judgemental equality of terms/types is alpha-beta-eta equivalence
instance JudgementalEq Term where
  (===) m n env = eval (resolve env m) == eval (resolve env n)

instance JudgementalEq BoundTerm where
  (===) m n env = evalBoundTerm (resolveBoundTerm env m) == evalBoundTerm (resolveBoundTerm env n)
    where
      evalBoundTerm :: BoundTerm -> BoundTerm
      evalBoundTerm (NoBind m) = NoBind (eval m)
      evalBoundTerm (Bind m)   = evalBoundTerm m

      resolveBoundTerm :: Environment -> BoundTerm -> BoundTerm
      resolveBoundTerm env (NoBind m) = NoBind (resolve env m)
      resolveBoundTerm env (Bind m)   = resolveBoundTerm env m
