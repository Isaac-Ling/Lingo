module Core.Term where

import Data.ByteString.Lazy.Char8 (ByteString)

data Explicitness
  = Exp
  | Imp
  deriving (Eq)

-- Named source terms --

type NamedAssumption = (ByteString, NamedTerm)
type NamedAlias = (ByteString, NamedTerm)

type NamedBinder = (ByteString, NamedTerm)

type NamedLambdaBinder = (ByteString, Maybe NamedTerm, Explicitness)
type NamedSigmaBinder = (Maybe ByteString, NamedTerm)
type NamedPiBinder = (Maybe ByteString, NamedTerm, Explicitness)

data NamedBoundTerm
  = NNoBind NamedTerm
  | NBind ByteString NamedBoundTerm

data NamedTerm
  = NVar ByteString
  | NLam NamedLambdaBinder NamedTerm
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
  | NUnivalence NamedTerm
  | NRefl NamedTerm
  | NPi NamedPiBinder NamedTerm
  | NIdFam NamedTerm
  | NId (Maybe NamedTerm) NamedTerm NamedTerm
  | NSigma NamedSigmaBinder NamedTerm
  | NInd NamedTerm NamedBoundTerm [NamedBoundTerm] NamedTerm

-- De Bruijn Terms --

data Var
  = Free ByteString
  | Bound Int
  | Meta Int
  deriving (Eq)

type Alias = (ByteString, Term)
type Environment = [Alias]

type Binder = (ByteString, Term)

type LambdaBinder = (ByteString, Maybe Term, Explicitness)
type SigmaBinder = (Maybe ByteString, Term)
type PiBinder = (Maybe ByteString, Term, Explicitness)

data BoundTerm
  = NoBind Term
  | Bind (Maybe ByteString) BoundTerm

data Term
  = Var Var
  | Lam LambdaBinder Term
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
  | Univalence Term
  | Refl Term
  | Pi PiBinder Term
  | IdFam Term
  | Id (Maybe Term) Term Term
  | Sigma SigmaBinder Term
  -- Induction principle is of the form: Ind <What am I inducting over?> <Motive> <Required evidence> <Antecedent>
  | Ind Term BoundTerm [BoundTerm] Term
