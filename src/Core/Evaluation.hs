module Core.Evaluation where

import Core.Data
import Data.ByteString.Lazy.Char8 (ByteString, pack)

isValue :: Term -> Bool
isValue (Lam _ _) = True
isValue e         = isNeutralTerm e

isNeutralTerm :: Term -> Bool
isNeutralTerm (Anno e _) = isNeutralTerm e
isNeutralTerm (Var _)    = True
isNeutralTerm (App e e') = isNeutralTerm e && isValue e'
isNeutralTerm _          = False

isFreeIn :: ByteString -> Term -> Bool
isFreeIn x (Anno e _) = x `isFreeIn` e
isFreeIn x (Var _)    = True
isFreeIn x (App e e') = (x `isFreeIn` e) && (x `isFreeIn` e')
isFreeIn x (Lam y e)
  | x == y            = False
  | otherwise         = x `isFreeIn` e

sub :: Term -> ByteString -> Term -> Term
sub t x (Anno e _) = sub t x e
sub t x (Var y)
  | x == y    = t
  | otherwise = Var y
sub t x (App e e') = App (sub t x e) (sub t x e')
sub t x (Lam y e)
  | x == y         = Lam y e
  | y `isFreeIn` t = Lam freshVar (sub t x (sub (Var freshVar) y e))
  | otherwise      = Lam y (sub t x e)
  where
-- TODO: Get fresh variable
    freshVar :: ByteString
    freshVar = pack "Bob"

beta :: Term -> Term
beta (Anno e _) = beta e
beta (App (Lam x e) e') = sub e' x e
beta e                  = e

eval :: Term -> Term
eval (Anno e _)     = eval e
eval (Var x)        = Var x
eval (Lam x e)      = Lam x (eval e)
eval (App e e')
  | isNeutralTerm f = App (eval e) (eval e')
  | otherwise       = eval (beta (App e e'))
  where
    f :: Term
    f = eval e
