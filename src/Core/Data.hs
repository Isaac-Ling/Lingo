module Core.Data where

import Data.ByteString.Lazy.Char8 (ByteString)

-- Typing context
type Assumption = (ByteString, Term)
type Context = [Assumption]

-- Evaluation environment
type Alias = (ByteString, Term)
type Environment = [Alias]

data Declaration
  = Anno Assumption
  | Def Alias

type Program = [Declaration]

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
  -- Induction principle is of the form: Ind <What am I inducting over?> <Motive> <Required evidence> <Term to prove>
  | Ind Term BoundTerm [BoundTerm] Term

data BoundTerm
  = NoBind Term
  | Bind ByteString BoundTerm
