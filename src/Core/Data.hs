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
  deriving Eq

instance Show Term where
  show (Var x)             = unpack x
  show Star                = "*"
  show (App e (Lam xt e')) = show e ++ " (" ++ show (Lam xt e') ++ ")"
  show (App (Lam xt e) e') = "(" ++ show (Lam xt e) ++ ") " ++ show e'
  show (App e e')          = show e ++ " " ++ show e'
  show (Lam (x, t) e)      = "\\(" ++ unpack x ++ " : " ++ show t ++ "). " ++ show e
  show (Univ i)            = "U" ++ show i
  show Zero                = "0"
  show One                 = "1"
