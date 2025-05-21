module Core.Term where

import Data.ByteString.Lazy.Char8 (ByteString)

-- Named source terms --

type NamedAssumption = (ByteString, NamedTerm)
type NamedAlias = (ByteString, NamedTerm)

data NamedLambdaBinding
  = NImp ByteString
  | NExp NamedAssumption

data NamedBoundTerm
  = NNoBind NamedTerm
  | NBind ByteString NamedBoundTerm

data NamedTerm
  = NVar ByteString
  | NLam NamedLambdaBinding NamedTerm
  | NApp NamedTerm NamedTerm
  | NStar
  | NPair NamedTerm NamedTerm
  | NUniv Int
  | NZero
  | NOne
  | NPi NamedAssumption NamedTerm
  | NArr NamedTerm NamedTerm
  | NSigma NamedAssumption NamedTerm
  | NProd NamedTerm NamedTerm
  | NInd NamedTerm NamedBoundTerm [NamedBoundTerm] NamedTerm

-- De Bruijn Terms --

data Var
  = Free ByteString
  | Bound Int

type Assumption = (ByteString, Term)
type Context = [Assumption]

type Alias = (ByteString, Term)
type Environment = [Alias]

data LambdaBinding
  = Imp ByteString
  | Exp Assumption

data BoundTerm
  = NoBind Term
  | Bind ByteString BoundTerm

data Term
  = Var Var
  | Lam LambdaBinding Term
  | App Term Term
  | Star
  | Pair Term Term
  | Univ Int
  | Zero
  | One
  | Pi Assumption Term
  | Sigma Assumption Term
  -- Induction principle is of the form: Ind <What am I inducting over?> <Motive> <Required evidence> <Antecedent>
  | Ind Term BoundTerm [BoundTerm] Term

class JudgementalEq a where
  (===) :: a -> a -> Environment -> Bool
