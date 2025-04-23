module Core.Evaluation where

import Core.Data
import Data.ByteString.Lazy.Char8 (ByteString, pack)

isValue :: Term -> Bool
isValue (Lam _ _) = True
isValue m                = isNeutralTerm m

isNeutralTerm :: Term -> Bool
isNeutralTerm (Var _)   = True
isNeutralTerm (App m n) = isNeutralTerm m && isValue n
isNeutralTerm Star      = True
isNeutralTerm (Univ _)  = True
isNeutralTerm Zero      = True
isNeutralTerm One       = True
isNeutralTerm _         = False

isFreeIn :: ByteString -> Term -> Bool
isFreeIn x (Var y)    = x == y
isFreeIn x (App m n) = (x `isFreeIn` m) && (x `isFreeIn` n)
isFreeIn x (Lam (y, _) m)
  | x == y            = False
  | otherwise         = x `isFreeIn` m
isFreeIn x m          = True

-- TODO: Make fresh var readable
getFreshVar :: Term -> ByteString
getFreshVar m = buildFreshVar m (pack "a")
  where
    buildFreshVar :: Term -> ByteString -> ByteString
    buildFreshVar (Var y)    x     = x <> y
    buildFreshVar (App m n) x     = buildFreshVar m x <> buildFreshVar n x
    buildFreshVar (Lam (y, _) m) x = buildFreshVar m (x <> y)
    buildFreshVar m x              = x

sub :: Term -> ByteString -> Term -> Term
sub t x (Var y)
  | x == y         = t
  | otherwise      = Var y
sub t x (App m n) = App (sub t x m) (sub t x n)
sub t x (Lam (y, t') m)
  | x == y         = Lam (y, t') m
  | y `isFreeIn` t = Lam (freshVar, t') (sub t x (sub (Var freshVar) y m))
  | otherwise      = Lam (y, t') (sub t x m)
  where
    freshVar :: ByteString
    freshVar = getFreshVar m
sub t x m          = m

beta :: Term -> Term
beta (App (Lam (x, t') m) n) = sub n x m
beta m                       = m

eval :: Term -> Term
eval (Var x)        = Var x

-- Eta expansion
eval (Lam (x, t) (App f (Var x')))
  | x == x'   = eval f
  | otherwise = Lam (x, eval t) (eval (App f (Var x')))

eval (Lam (x, t) m) = Lam (x, eval t) (eval m)
eval (Pi (x, t) m)  = Pi (x, eval t) (eval m)
eval (App m n)
  | isNeutralTerm f = App f (eval n)
  | otherwise       = eval (beta (App f n))
  where
    f :: Term
    f = eval m
eval m              = m
