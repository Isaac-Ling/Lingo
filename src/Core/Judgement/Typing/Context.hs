module Core.Judgement.Typing.Context where

import Core.Term
import Core.Error
import Core.Judgement.Utils

import Data.Bifunctor (second)
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.ByteString.Lazy.Char8 (ByteString)

type Assumption = (ByteString, Term)
type Context = [Assumption]

-- This context records the type of bound variables, where the ith type in the
-- context is the type of the ith binder away from the current term
type BoundContext = [(Maybe ByteString, Term)]

-- A constraint is an equality of the first term with the second in a specified context
type Constraint = (BoundContext, Term, Term)
type Constraints = [Constraint]

data MetaState = MetaState
  { csts   :: Constraints
  , mctx   :: MetaContext
  , metaID :: Int
  } deriving (Show)

type MetaContext   = [(Int, Term)]

data Contexts = Contexts
  { env   :: Environment
  , ctx   :: Context
  , bctx  :: BoundContext
  , tbctx :: BoundContext
  } deriving (Show)

type TypeCheck a = ReaderT Contexts (StateT MetaState CanError) a

typeError :: ErrorCode -> Maybe String -> TypeCheck a
typeError errc ms = lift $ lift $ Error errc ms

showTermWithContext :: BoundContext -> Term -> String
showTermWithContext bctx = showTermWithBinders (map fst bctx)

addToCtx :: Assumption -> (Contexts -> Contexts)
addToCtx (x, t) ctxs = ctxs { ctx=(x, t) : ctx ctxs }

addToBoundCtx :: (Maybe ByteString, Term) -> (Contexts -> Contexts)
addToBoundCtx (x, t) ctxs = ctxs { bctx=(x, bumpUp t) : map (second bumpUp) (bctx ctxs) }

addToTypeBoundCtx :: (Maybe ByteString, Term) -> (Contexts -> Contexts)
addToTypeBoundCtx (x, t) ctxs = ctxs { tbctx=(x, bumpUp t) : map (second bumpUp) (tbctx ctxs) }

addToBoundCtxs :: (Maybe ByteString, Term) -> (Maybe ByteString, Term) -> (Contexts -> Contexts)
addToBoundCtxs (x, t) (x', t') = addToTypeBoundCtx (x', t') . addToBoundCtx (x, t)

useTypeBoundCtx :: Contexts -> Contexts
useTypeBoundCtx ctxs = ctxs { bctx=tbctx ctxs }

createMetaVar :: Term -> TypeCheck Term
createMetaVar mt = do
  st <- get
  let mid = metaID st
  put st { metaID=mid + 1, mctx=(mid, mt) : mctx st }

  return $ Var $ Meta mid
