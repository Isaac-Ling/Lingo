module Core.Evaluation where

import Core.Data
import Data.ByteString.Lazy.Char8 (ByteString, pack)

isValue :: Term -> Bool
isValue (Lam _ _) = True
isValue e         = isNeutralTerm e

isNeutralTerm :: Term -> Bool
isNeutralTerm (Anno e _) = isNeutralTerm e
isNeutralTerm (Var _)    = True
isNeutralTerm Star       = True
isNeutralTerm (Flag _)   = True
isNeutralTerm (App e e') = isNeutralTerm e && isValue e'
isNeutralTerm _          = False

isFreeIn :: ByteString -> Term -> Bool
isFreeIn x (Anno e _) = x `isFreeIn` e
isFreeIn x (Var y)    = x == y
isFreeIn x (App e e') = (x `isFreeIn` e) && (x `isFreeIn` e')
isFreeIn x (Lam (VarAnno y _) e)
  | x == y            = False
  | otherwise         = x `isFreeIn` e
isFreeIn x e          = True

-- TODO: Make fresh var readable
getFreshVar :: Term -> ByteString
getFreshVar e = buildFreshVar e (pack "")
  where
    buildFreshVar :: Term -> ByteString -> ByteString
    buildFreshVar (Anno e _) x            = buildFreshVar e x
    buildFreshVar (Var y)    x            = x <> y
    buildFreshVar (App e e') x            = buildFreshVar e x <> buildFreshVar e' x
    buildFreshVar (Lam (VarAnno y _) e) x = buildFreshVar e (x <> y)
    buildFreshVar e x                     = x

sub :: Term -> ByteString -> Term -> Term
sub t x (Anno e _) = sub t x e
sub t x (Var y)
  | x == y         = t
  | otherwise      = Var y
sub t x (App e e') = App (sub t x e) (sub t x e')
sub t x (Lam (VarAnno y t') e)
  | x == y         = Lam (VarAnno y t') e
  | y `isFreeIn` t = Lam (VarAnno freshVar t') (sub t x (sub (Var freshVar) y e))
  | otherwise      = Lam (VarAnno y t') (sub t x e)
  where
    freshVar :: ByteString
    freshVar = getFreshVar e
sub t x e          = e

beta :: Term -> Term
beta (Anno e _)                      = beta e
beta (App (Lam (VarAnno x t') e) e') = sub e' x e
beta e                               = e

eval :: Term -> Term
eval (Anno e _)            = eval e
eval (Var x)               = Var x
eval (Lam (VarAnno x t) e) = Lam (VarAnno x t) (eval e)
eval (App e e')
  | isNeutralTerm f        = App f (eval e')
  | otherwise              = eval (beta (App f e'))
  where
    f :: Term
    f = eval e
eval e                     = e
