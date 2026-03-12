module Core.Term where

import Data.ByteString.Lazy.Char8 (ByteString)

data Explicitness
  = Exp
  | Imp
  deriving (Eq, Show)

-- A list of binders, where the ith element is the ith binder away from the
-- current term. Nothing is used if we should never match against that binder
type Binders = [Maybe ByteString]

-- Source terms --

type SourceAssumption = (ByteString, SourceTerm)
type SourceAlias = (ByteString, SourceTerm)

type SourceBinder = (ByteString, SourceTerm)

type SourceLambdaBinder = (ByteString, Maybe SourceTerm, Explicitness)
type SourceSigmaBinder = (Maybe ByteString, SourceTerm)
type SourcePiBinder = (Maybe ByteString, SourceTerm, Explicitness)

data Parameter
  = BinderParam SourceLambdaBinder 
  | Pattern SourceTerm
  deriving (Show, Eq)

data SourceBoundTerm
  = SNoBind SourceTerm
  | SBind ByteString SourceBoundTerm
  deriving (Show, Eq)

data SourceTerm
  = SVar ByteString
  | SLam SourceLambdaBinder SourceTerm
  | SApp SourceTerm (SourceTerm, Explicitness)
  | SStar
  | SPair SourceTerm SourceTerm
  | SUniv (Maybe Int)
  | SBot
  | STop
  | SNat
  | SZero
  | SSucc SourceTerm
  | SSum SourceTerm SourceTerm
  | SInr SourceTerm
  | SInl SourceTerm
  | SFunext SourceTerm
  | SUnivalence SourceTerm
  | SRefl (Maybe SourceTerm)
  | SPi SourcePiBinder SourceTerm
  | SIdFam SourceTerm
  | SId (Maybe SourceTerm) SourceTerm SourceTerm
  | SSigma SourceSigmaBinder SourceTerm
  | SInd SourceTerm SourceBoundTerm [SourceBoundTerm] SourceTerm
  | SParamTerm [Parameter] SourceTerm
  -- Substitution terms are emitted by the elaborator: for each
  -- pair in the list, the first term will be substituted for the
  -- second var when converted to a core term
  | SubstitutionTerm [(SourceTerm, ByteString)] SourceTerm
  deriving (Show, Eq)

-- Core Terms --

data Var
  = Free ByteString
  | Bound Int
  | Meta Int

data Universe
  = ULvl Int
  | UVar Int
  | UFlex
  deriving Eq

instance Eq Var where
  Free x == Free y   = x == y
  Bound i == Bound j = i == j
  Meta i == Meta j   = i == j
  _ == _             = False

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
  | App Term (Term, Explicitness)
  | Star
  | Pair Term Term
  | Univ Universe
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
  | Refl (Maybe Term)
  | Pi PiBinder Term
  | IdFam Term
  | Id (Maybe Term) Term Term
  | Sigma SigmaBinder Term
  -- Induction principle is of the form: Ind <What am I inducting over?> <Motive> <Required evidence> <Antecedent>
  | Ind Term BoundTerm [BoundTerm] Term
