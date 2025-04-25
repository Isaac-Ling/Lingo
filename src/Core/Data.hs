module Core.Data where

import Data.ByteString.Lazy.Char8 (ByteString)

type Assumption = (ByteString, Term)

type Context = [Assumption]

data Term
  = Var ByteString
  | Lam Assumption Term
  | App Term Term
  | Star
  | Pair Term Term
  | Univ Integer
  | Zero
  | One
  | Pi Assumption Term
  | Sigma Assumption Term
