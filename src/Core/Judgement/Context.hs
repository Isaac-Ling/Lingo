module Core.Judgement.Context where

import Core.Term
import Core.Error

import Data.List ((!?))
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.ByteString.Lazy.Char8 (ByteString, pack)

data TermData = TermData
  { eterm :: Term
  , ecsts :: UnivConstraints
  }

type Assumption = (ByteString, TermData)
type Context = [Assumption]

type EnvEntry = (ByteString, TermData)
type Environment = [EnvEntry]

-- This context records the type of bound variables, where the ith type in the
-- context is the type of the ith binder away from the current term
type BoundContext = [(Maybe ByteString, Term)]

-- A constraint is an equality of the first term with the second in a specified context
type Constraint = (BoundContext, Term, Term)
type Constraints = [Constraint]

-- A universe constraint is an imposed ordering on universe metas
data UnivConstraint
  = ULeq Universe Universe
  | ULt Universe Universe

type UnivConstraints = [UnivConstraint]

data TypeCheckState = TypeCheckState
  { mcsts   :: Constraints
  , ucsts   :: UnivConstraints
  , mctx    :: MetaContext
  , metaID  :: Int
  , univID  :: Int
  }

data MetaData = MetaData
  { mtype :: Term
  , mbctx :: BoundContext
  }

type MetaContext = [(Int, MetaData)]

data Contexts = Contexts
  { env   :: Environment
  , ctx   :: Context
  , bctx  :: BoundContext
  , tbctx :: BoundContext
  }

type TypeCheck a = ReaderT Contexts (StateT TypeCheckState CanError) a

typeError :: ErrorCode -> Maybe String -> TypeCheck a
typeError errc ms = lift $ lift $ Error errc ms

addToCtx :: Assumption -> (Contexts -> Contexts)
addToCtx (x, t) ctxs = ctxs { ctx=(x, t) : ctx ctxs }

addToBoundCtx :: (Maybe ByteString, Term) -> (Contexts -> Contexts)
addToBoundCtx (x, t) ctxs = ctxs { bctx=(x, t) : bctx ctxs }

addToTypeBoundCtx :: (Maybe ByteString, Term) -> (Contexts -> Contexts)
addToTypeBoundCtx (x, t) ctxs = ctxs { tbctx=(x, t) : tbctx ctxs }

addToBoundCtxs :: (Maybe ByteString, Term) -> (Maybe ByteString, Term) -> (Contexts -> Contexts)
addToBoundCtxs (x, t) (x', t') = addToTypeBoundCtx (x', t') . addToBoundCtx (x, t)

useTypeBoundCtx :: Contexts -> Contexts
useTypeBoundCtx ctxs = ctxs { bctx=tbctx ctxs }

useBoundCtx :: Contexts -> Contexts
useBoundCtx ctxs = ctxs { tbctx=bctx ctxs }

createUnivVar :: TypeCheck Universe
createUnivVar = do
  st <- get
  let uid = univID st
  put st { univID=uid + 1 }
  return $ UVar uid

createMetaVar :: BoundContext -> Term -> TypeCheck Term
createMetaVar bc mt = do
  st <- get
  let mid = metaID st
  -- Apply metavariable to the context to avoid scoping issues
  (metaAppliedToCtx, mtype) <- applyToCtx bc (Var $ Meta mid) mt
  put st { metaID=mid + 1, mctx=(mid, MetaData { mtype=mtype, mbctx=bc }) : mctx st }

  let n = length bc

  return metaAppliedToCtx
  where
    applyToCtx :: BoundContext -> Term -> Term -> TypeCheck (Term, Term)
    applyToCtx bc m mt = go bc (length bc - 1) m mt
      where
        go :: BoundContext -> Int -> Term -> Term -> TypeCheck (Term, Term)
        go bc i m mt
          | i < 0     = return (m, mt)
          | otherwise = case bc !? i of
            Just (x, t) -> do
              (m', t') <- go bc (i - 1) (App m (Var $ Bound i, Exp)) mt
              return (m', Pi (x, t, Exp) t')
            Nothing     -> typeError FailedToInferType $ Just "Missing type for bound term"
