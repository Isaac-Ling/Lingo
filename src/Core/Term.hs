module Core.Term where

import Data.ByteString.Lazy.Char8 (ByteString)

-- Named source terms --

type NamedAssumption = (ByteString, NamedTerm)
type NamedAlias = (ByteString, NamedTerm)

type NamedLambdaBinding = (ByteString, Maybe NamedTerm)
type NamedAnonBinder = (Maybe ByteString, NamedTerm)

data NamedBoundTerm
  = NNoBind NamedTerm
  | NBind ByteString NamedBoundTerm

data NamedTerm
  = NVar ByteString
  | NLam NamedLambdaBinding NamedTerm
  | NApp NamedTerm NamedTerm
  | NStar
  | NPair NamedTerm NamedTerm
  | NUniv Integer
  | NBot
  | NTop
  | NNat
  | NZero
  | NSucc NamedTerm
  | NSum NamedTerm NamedTerm
  | NInr NamedTerm
  | NInl NamedTerm
  | NFunext NamedTerm
  | NRefl NamedTerm
  | NPi NamedAnonBinder NamedTerm
  | NIdFam NamedTerm
  | NId (Maybe NamedTerm) NamedTerm NamedTerm
  | NSigma NamedAnonBinder NamedTerm
  | NInd NamedTerm NamedBoundTerm [NamedBoundTerm] NamedTerm

-- De Bruijn Terms --

data Var
  = Free ByteString
  | Bound Int

type Assumption = (ByteString, Term)
type Context = [Assumption]

type Alias = (ByteString, Term)
type Environment = [Alias]

type LambdaBinding = (ByteString, Maybe Term)
type AnonBinder = (Maybe ByteString, Term)

data BoundTerm
  = NoBind Term
  | Bind (Maybe ByteString) BoundTerm

data Term
  = Var Var
  | Lam LambdaBinding Term
  | App Term Term
  | Star
  | Pair Term Term
  | Univ Integer
  | Bot
  | Top
  | Nat
  | Zero
  | Succ Term
  | Sum Term Term
  | Inl Term
  | Inr Term
  | Funext Term
  | Refl Term
  | Pi AnonBinder Term
  | IdFam Term
  | Id (Maybe Term) Term Term
  | Sigma AnonBinder Term
  -- Induction principle is of the form: Ind <What am I inducting over?> <Motive> <Required evidence> <Antecedent>
  | Ind Term BoundTerm [BoundTerm] Term
