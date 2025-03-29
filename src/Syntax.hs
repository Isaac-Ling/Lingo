module Syntax (Term (..), Program) where

data Term
  = Var String
  | Lam String Term
  | App Term Term
  deriving (Eq, Show)

-- A program is currently just a single lambda term to normalise
type Program = Term
