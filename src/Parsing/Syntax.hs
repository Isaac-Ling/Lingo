module Parsing.Syntax (Term (..), Program) where

import Data.ByteString.Lazy.Char8 (ByteString)

data Term
  = Var ByteString
  | Lam ByteString Term
  | App Term Term
  deriving (Eq, Show)

-- A program is just a single lambda term to normalise
type Program = Term
