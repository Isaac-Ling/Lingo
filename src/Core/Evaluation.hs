module Core.Evaluation where

import Core.Data
import Data.ByteString.Lazy.Char8 (ByteString, pack, unpack)

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
isFreeIn x (Var y)   = x == y
isFreeIn x (App m n) = (x `isFreeIn` m) && (x `isFreeIn` n)
isFreeIn x (Lam (y, _) m)
  | x == y           = False
  | otherwise        = x `isFreeIn` m
isFreeIn x (Pi (y, _) m)
  | x == y           = False
  | otherwise        = x `isFreeIn` m
isFreeIn x (Sigma (y, _) m)
  | x == y           = False
  | otherwise        = x `isFreeIn` m
isFreeIn x m         = False

isFreeInBound :: ByteString -> BoundTerm -> Bool
isFreeInBound x (Bind y t) = if x == y then False else isFreeInBound x t
isFreeInBound x (NoBind t) = isFreeIn x t

-- TODO: Make fresh var readable
getFreshVar :: Term -> ByteString
getFreshVar m = buildFreshVar m (pack "a")
  where
    buildFreshVar :: Term -> ByteString -> ByteString
    buildFreshVar (Var y)    x       = x <> y
    buildFreshVar (App m n) x        = buildFreshVar m x <> buildFreshVar n x
    buildFreshVar (Lam (y, _) m) x   = buildFreshVar m (x <> y)
    buildFreshVar (Pi (y, _) m) x    = buildFreshVar m (x <> y)
    buildFreshVar (Sigma (y, _) m) x = buildFreshVar m (x <> y)
    buildFreshVar m x                = x

sub :: Term -> ByteString -> Term -> Term
sub t x (Var y)
  | x == y         = t
  | otherwise      = Var y
sub t x (App m n) = App (sub t x m) (sub t x n)
sub t x (Lam (y, t') m)
  | x == y         = Lam (y, t') m
  | y `isFreeIn` t = Lam (freshVar, sub t x t') (sub t x (sub (Var freshVar) y m))
  | otherwise      = Lam (y, sub t x t') (sub t x m)
  where
    freshVar :: ByteString
    freshVar = getFreshVar m
sub t x (Pi (y, t') m)
  | x == y         = Pi (y, t') m
  | y `isFreeIn` t = Pi (freshVar, sub t x t') (sub t x (sub (Var freshVar) y m))
  | otherwise      = Pi (y, sub t x t') (sub t x m)
  where
    freshVar :: ByteString
    freshVar = getFreshVar m
sub t x (Sigma (y, t') m)
  | x == y         = Sigma (y, t') m
  | y `isFreeIn` t = Sigma (freshVar, sub t x t') (sub t x (sub (Var freshVar) y m))
  | otherwise      = Sigma (y, sub t x t') (sub t x m)
  where
    freshVar :: ByteString
    freshVar = getFreshVar m
sub t x (Pair m n) = Pair (sub t x m) (sub t x n)
sub t x m          = m

beta :: Term -> Term
beta (App (Lam (x, t') m) n) = sub n x m
beta m                       = m

eval :: Term -> Term
eval (Var x)        = Var x
eval (Lam (x, t) (App f (Var x')))
  | x == x'   = eval f -- Eta expansion
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

instance Show Term where
  show (Var x)                          = unpack x
  show Star                             = "*"
  show (App (Lam xt m) (Lam yt n))      = "(" ++ show (Lam xt m) ++ ") " ++ "(" ++ show (Lam yt n) ++ ")"
  show (App m (Lam xt n))               = show m ++ " (" ++ show (Lam xt n) ++ ")"
  show (App (Lam xt m) n)               = "(" ++ show (Lam xt m) ++ ") " ++ show n
  show (App (Pi xt m) n)                = "(" ++ show (Pi xt m) ++ ") " ++ show n
  show (App (Sigma xt m) n)             = "(" ++ show (Sigma xt m) ++ ") " ++ show n
  show (App m n)                        = show m ++ " " ++ show n
  show (Pair m n)                       = "(" ++ show m ++ ", " ++ show n ++ ")"
  show (Lam (x, t) m)                   = "\\(" ++ unpack x ++ " : " ++ show t ++ "). " ++ show m
  show (Univ 0)                         = "U"
  show (Univ i)                         = "U" ++ show i
  show Zero                             = "0"
  show One                              = "1"
  show (Pi (x, Pi (y, t') m) n)         = "(" ++ show (Pi (y, t') m) ++ ")" ++ " -> " ++ show n
  show (Pi (x, t) m)
    | x `isFreeIn` m                    = "(" ++ unpack x ++ " : " ++ show t ++ ") -> " ++ show m
    | otherwise                         = show t ++ " -> " ++ show m
  show (Sigma (x, t) (Sigma (y, t') m))
    | x `isFreeIn` Sigma (y, t') m      = showSigmaOperarands t ++ " x (" ++ show (Sigma (y, t') m) ++ show ")"
    | otherwise                         = "(" ++ unpack x ++ " : " ++ show t ++ ") x " ++ "(" ++ show (Sigma (y, t') m) ++ ")"
  show (Sigma (x, t) m)
    | x `isFreeIn` m                    = "(" ++ unpack x ++ " : " ++ show t ++ ") x " ++ showSigmaOperarands m
    | otherwise                         = showSigmaOperarands t ++ " x " ++ showSigmaOperarands m
  show (Ind t m e a)                    = "ind[" ++ show t ++ "](" ++ show m ++ ", " ++ showListNoParen e ++ ", " ++ show a ++ ")"

showListNoParen :: Show a => [a] -> String
showListNoParen []     = ""
showListNoParen [x]    = show x
showListNoParen (x:xs) = show x ++ ", " ++ showListNoParen xs

-- TODO: Generalise this to support arbitrary terms with any precedence
showSigmaOperarands :: Term -> String
showSigmaOperarands (App m n)     = "(" ++ show (App m n) ++ ")"
showSigmaOperarands (Pi (x, t) m) = "(" ++ show (Pi (x, t) m) ++ ")"
showSigmaOperarands m             = show m

instance Show BoundTerm where
  show (Bind x t) = unpack x ++ ". " ++ show t
  show (NoBind t) = show t
