module Core.Data where

import Data.ByteString.Lazy.Char8 (ByteString, unpack)

type Assumption = (ByteString, Term)

type Context = [Assumption]

data Term
  = Var ByteString
  | Lam Assumption Term
  | App Term Term
  | Star
  | Univ Int
  | Zero
  | One
  | Pi Assumption Term
  deriving Eq

instance Show Term where
  show (Var x)            = unpack x
  show Star               = "*"
  show (App m (Lam xt n)) = show m ++ " (" ++ show (Lam xt n) ++ ")"
  show (App (Lam xt m) n) = "(" ++ show (Lam xt m) ++ ") " ++ show n
  show (App (Pi xt m) n)  = "(" ++ show (Pi xt m) ++ ") " ++ show n
  show (App m n)          = show m ++ " " ++ show n
  show (Lam (x, t) m)     = "\\(" ++ unpack x ++ " : " ++ show t ++ "). " ++ show m
  show (Univ i)           = "U" ++ show i
  show Zero               = "0"
  show One                = "1"
  show (Pi (x, t) m)      = "(" ++ unpack x ++ " : " ++ show t ++ ") -> " ++ show m
