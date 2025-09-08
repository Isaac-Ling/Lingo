module Core.Judgement.Typing.Type (inferType, checkType) where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation
import Core.Judgement.Typing.Context
import Core.Judgement.Typing.Inference
import Core.Judgement.Typing.Unification

import Control.Monad.Reader
import Control.Monad.State.Lazy

inferType :: Environment -> Context -> Term -> CanError (Term, Term)
inferType env ctx m = do
  result <- runStateT (runReaderT (runInferType m) initContexts) initState
  msol   <- solveConstraints env ctx (mctx $ snd result) (mcsts $ snd result)
  let ts = fst result
  let e  = expandMetas msol $ fst ts
  let t  = expandMetas msol $ snd ts
  return (e, t)
  where
    initContexts = Contexts { env=env, ctx=ctx, bctx=[], tbctx=[] }
    initState    = MetaState { mcsts=[], mctx=[], metaID=0 }

checkType :: Environment-> Context -> Term -> Term -> CanError (Term, Term)
checkType env ctx m t = do
  result <- runStateT (runReaderT (runCheckType m $ eval $ resolve env t) initContexts) initState
  msol   <- solveConstraints env ctx (mctx $ snd result) (mcsts $ snd result)
  let ts = fst result
  let e  = expandMetas msol $ fst ts
  let t  = expandMetas msol $ snd ts
  return (e, t)
  where
    initContexts = Contexts { env=env, ctx=ctx, bctx=[], tbctx=[] }
    initState    = MetaState { mcsts=[], mctx=[], metaID=0 }
