module Core.Judgement.Evaluation where

import Core.Term
import Core.Error
import Core.Judgement.Utils

import Data.ByteString.Lazy.Char8 (ByteString, pack)

eval :: Term -> Term
eval (Lam _ (App f (Var (Bound 0))))                                  = eval $ bumpDown f -- Eta conversion
eval (Lam (x, Just t) m)                                              = Lam (x, Just $ eval t) (eval m)
eval (Lam (x, Nothing) m)                                             = Lam (x, Nothing) (eval m)
eval (Pi (x, t) m)                                                    = Pi (x, eval t) (eval m)
eval (Sigma (x, t) m)                                                 = Sigma (x, eval t) (eval m)
eval (Pair m n)                                                       = Pair (eval m) (eval n)
eval (App m n)
  | isNeutral f = App f (eval n)
  | otherwise   = eval (beta (App f n))
  where
    f :: Term
    f = eval m
eval (Ind One _ [NoBind c] _)                                         = c
-- TODO: Don't turn bound terms into lambdas to evaluate
eval (Ind (Sigma _ _) _ [Bind w (Bind y (NoBind f))] (Pair a b))      = eval $ App (App (Lam (pack "w", Nothing) $ Lam (pack "y", Nothing) f) a) b
eval (Ind (Sum _ _) _ [Bind x (NoBind c), Bind y (NoBind d)] (Inl a)) = eval $ App (Lam (pack "x", Nothing) c) a
eval (Ind (Sum _ _) _ [Bind x (NoBind c), Bind y (NoBind d)] (Inr b)) = eval $ App (Lam (pack "y", Nothing) d) b
eval (Ind t m c a)
  | isValue $ Ind t m c a = Ind t m c a
  | otherwise             = eval $ Ind (eval t) (evalBoundTerm m) (map evalBoundTerm c) (eval a)
  where
    evalBoundTerm :: BoundTerm -> BoundTerm
    evalBoundTerm (NoBind m) = NoBind $ eval m
    evalBoundTerm (Bind x m) = Bind x $ evalBoundTerm m
eval m                                                                = m

isValue :: Term -> Bool
isValue (Lam _ _) = True
isValue m         = isNeutral m

isNeutral :: Term -> Bool
isNeutral (Var x)          = True
isNeutral (App m n)        = isNeutral m && isValue n
isNeutral (Pi (_, t) m)    = isValue t && isValue m
isNeutral (Sigma (_, t) m) = isValue t && isValue m
isNeutral (Sum m n)        = isValue m && isValue n
isNeutral (Pair m n)       = isValue m && isValue n
isNeutral Star             = True
isNeutral (Univ _)         = True
isNeutral Zero             = True
isNeutral One              = True
isNeutral (Inl m)          = isValue m
isNeutral (Inr m)          = isValue m
isNeutral (Ind t m c a)    = isValue t && isBoundTermValue m && all isBoundTermValue c && isValue a
  where
    isBoundTermValue :: BoundTerm -> Bool
    isBoundTermValue (NoBind m) = isValue m
    isBoundTermValue (Bind _ m) = isBoundTermValue m
isNeutral _                = False

beta :: Term -> Term
beta (App (Lam _ m) n) = bumpDown $ open (bumpUp n) m
beta m                 = m

equal :: Environment -> Term -> Term -> Bool
equal env m n = elaborate env m == elaborate env n

-- Equality of terms is alpha-beta-eta equivalence
instance Eq Term where
  m == n = eval m === eval n
    where
      Var x === Var y                           = x == y
      Lam (_, Nothing) m === Lam (_, Nothing) n = m == n
      Lam (_, Just t) m === Lam (_, Just t') n  = t == t' && m == n
      App m n === App m' n'                     = m == m' && n == n'
      Star === Star                             = True
      Pair m n === Pair m' n'                   = m == m' && n == n'
      Univ i === Univ j                         = i == j
      Zero === Zero                             = True
      One === One                               = True
      Sum m n === Sum m' n'                     = m == m && n' == n'
      Pi (_, t) m === Pi (_, t') n              = t == t' && m == n
      Sigma (_, t) m === Sigma (_, t') n        = t == t' && m == n
      Ind t m c a === Ind t' m' c' a'           = t == t' && m == m' && c == c' && a == a' 
      _ === _                                   = False

instance Eq BoundTerm where
  NoBind m == NoBind n = m == n
  Bind _ m == Bind _ n = m == n
  _ == _               = False

instance Eq Var where
  Free x == Free y   = x == y
  Bound i == Bound j = i == j
  _ == _             = False
