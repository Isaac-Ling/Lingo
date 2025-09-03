module Core.Judgement.Evaluation where

import Core.Term
import Core.Error
import Core.Judgement.Utils

import Data.ByteString.Lazy.Char8 (ByteString, pack)

eval :: Term -> Term
eval (Lam _ (App f (Var (Bound 0), _)))                               = eval $ bumpDown f -- Eta conversion
eval (Lam (x, Just t, ex) m)                                          = Lam (x, Just $ eval t, ex) (eval m)
eval (Lam (x, Nothing, ex) m)                                         = Lam (x, Nothing, ex) (eval m)
eval (Pi (x, t, ex) m)                                                = Pi (x, eval t, ex) (eval m)
eval (Sigma (x, t) m)                                                 = Sigma (x, eval t) (eval m)
eval (Pair m n)                                                       = Pair (eval m) (eval n)
eval (Sum m n)                                                        = Sum (eval m) (eval n)
eval (Inl m)                                                          = Inl $ eval m
eval (Inr n)                                                          = Inr $ eval n
eval (Succ m)                                                         = Succ $ eval m
eval (IdFam t)                                                        = IdFam $ eval t
eval (Refl m)                                                         = Refl $ eval m
eval (App (App (IdFam t) (m, _)) (n, _))                              = eval $ Id (Just t) m n
eval (Id mt m n)                                                      = Id (fmap eval mt) (eval m) (eval n)
eval (App m (n, ex))
  | isNeutral f = App f (eval n, ex)
  | otherwise   = eval $ beta $ App f (n, ex)
  where
    f = eval m
eval (Ind Top _ [NoBind c] _)                                         = eval c
eval (Ind (Sigma _ _) _ [Bind w (Bind y (NoBind f))] (Pair a b))      = eval $ App (App (Lam (pack "w", Nothing, Exp) $ Lam (pack "y", Nothing, Exp) f) (a, Exp)) (b, Exp)
eval (Ind (Sum _ _) _ [Bind x (NoBind c), Bind y (NoBind d)] (Inl a)) = eval $ App (Lam (pack "x", Nothing, Exp) c) (a, Exp)
eval (Ind (Sum _ _) _ [Bind x (NoBind c), Bind y (NoBind d)] (Inr b)) = eval $ App (Lam (pack "y", Nothing, Exp) d) (b, Exp)
eval (Ind Nat _ [NoBind c0, _] Zero)                                  = eval c0
eval (Ind Nat m [c0, Bind x (Bind y (NoBind cs))] (Succ n))           = eval $ App (App (Lam (pack "x", Nothing, Exp) $ Lam (pack "y", Nothing, Exp) cs) (n, Exp)) (Ind Nat m [c0, Bind x (Bind y (NoBind cs))] n, Exp)
eval (Ind (IdFam t) m [Bind z (NoBind c), NoBind a, NoBind a'] (Refl a''))
  | a == a' && a' == a'' = eval $ App (Lam (pack "z", Nothing, Exp) c) (a, Exp)
  | otherwise            = Ind (IdFam t) m [Bind z $ NoBind c, NoBind a, NoBind a'] (Refl a'')
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
isNeutral (Var x)                                                               = True
isNeutral (App m (n, _))                                                        = isNeutral m && isValue n
isNeutral (Pi (_, t, _) m)                                                      = isValue t && isValue m
isNeutral (Sigma (_, t) m)                                                      = isValue t && isValue m
isNeutral (Sum m n)                                                             = isValue m && isValue n
isNeutral (Pair m n)                                                            = isValue m && isValue n
isNeutral Star                                                                  = True
isNeutral (Univ _)                                                              = True
isNeutral Bot                                                                   = True
isNeutral Top                                                                   = True
isNeutral Nat                                                                   = True
isNeutral Zero                                                                  = True
isNeutral (IdFam t)                                                             = isValue t
isNeutral (Id mt m n)                                                           = maybe True isValue mt && isValue m && isValue n
isNeutral (Inl m)                                                               = isValue m
isNeutral (Inr m)                                                               = isValue m
isNeutral (Refl m)                                                              = isValue m
isNeutral (Succ n)                                                              = isValue n
isNeutral (Funext p)                                                            = isValue p
isNeutral (Univalence a)                                                        = isValue a
isNeutral (Ind Top _ [NoBind _] _)                                              = False
isNeutral (Ind (Sigma _ _) _ [Bind w (Bind y (NoBind f))] (Pair a b))           = False
isNeutral (Ind (Sum _ _) _ [Bind x (NoBind c), Bind y (NoBind d)] (Inl a))      = False
isNeutral (Ind (Sum _ _) _ [Bind x (NoBind c), Bind y (NoBind d)] (Inr b))      = False
isNeutral (Ind Nat _ [NoBind c0, _] Zero)                                       = False
isNeutral (Ind Nat m [c0, Bind x (Bind y (NoBind cs))] (Succ n))                = False
isNeutral (Ind (IdFam t) m [Bind z (NoBind c), NoBind a, NoBind a'] (Refl a'')) = a == a' && a' == a''
isNeutral (Ind t m c a)                                                         = isValue t && isBoundTermValue m && all isBoundTermValue c && isValue a
  where
    isBoundTermValue :: BoundTerm -> Bool
    isBoundTermValue (NoBind m) = isValue m
    isBoundTermValue (Bind _ m) = isBoundTermValue m
isNeutral _                = False

beta :: Term -> Term
beta (App (Lam _ m) (n, _)) = bumpDown $ open (bumpUp n) m
beta m                      = m

equal :: Environment -> Term -> Term -> Bool
equal env m n = resolve env m == resolve env n

-- Equality of terms is modulo alpha-beta-eta equivalence
instance Eq Term where
  m == n = eval m === eval n
    where
      Var x === Var y                                 = x == y
      Lam (_, Nothing, _) m === Lam (_, Nothing, _) n = m == n
      Lam (_, Just t, _) m === Lam (_, Just t', _) n  = t == t' && m == n
      App m n === App m' n'                           = m == m' && n == n'
      Star === Star                                   = True
      Pair m n === Pair m' n'                         = m == m' && n == n'
      Univ i === Univ j                               = i == j
      Nat === Nat                                     = True
      Bot === Bot                                     = True
      Top === Top                                     = True
      Zero === Zero                                   = True
      Succ m === Succ n                               = m == n
      Funext p === Funext q                           = p == q
      Univalence a === Univalence b                   = a == b
      Sum m n === Sum m' n'                           = m == m' && n == n'
      IdFam t === IdFam t'                            = t == t'
      Id _ m n === Id _ m' n'                         = m == m' && n == n'
      Refl m === Refl n                               = m == n
      Pi (_, t, _) m === Pi (_, t', _) n              = t == t' && m == n
      Sigma (_, t) m === Sigma (_, t') n              = t == t' && m == n
      Ind t m c a === Ind t' m' c' a'                 = t == t' && m == m' && c == c' && a == a'
      _ === _                                         = False

instance Eq BoundTerm where
  NoBind m == NoBind n = m == n
  Bind _ m == Bind _ n = m == n
  _ == _               = False
