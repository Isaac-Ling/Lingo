module Core.Term where

import Data.ByteString.Lazy.Char8 (ByteString)

type Assumption = (ByteString, Term)

-- Typing context
type Context = [Assumption]

-- Evaluation environment
type Alias = (ByteString, Term)
type Environment = [Alias]

data LambdaBinding
  = Imp ByteString
  | Exp Assumption

data BoundTerm
  = NoBind Term
  | Bind ByteString BoundTerm

data Term
  = Var ByteString
  | Lam LambdaBinding Term
  | App Term Term
  | Star
  | Pair Term Term
  | Univ Integer
  | Zero
  | One
  | Pi Assumption Term
  | Sigma Assumption Term
  -- Induction principle is of the form: Ind <What am I inducting over?> <Motive> <Required evidence> <Antecedent>
  | Ind Term BoundTerm [BoundTerm] Term

class JudgementalEq a where
  (===) :: a -> a -> Environment -> Bool
