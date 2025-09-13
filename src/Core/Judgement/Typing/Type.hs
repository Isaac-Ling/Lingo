module Core.Judgement.Typing.Type where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation
import Core.Judgement.Typing.Context
import Core.Judgement.Typing.Inference
import Core.Judgement.Typing.Unification

import Control.Monad.Reader
import Control.Monad.State.Lazy

inferTypeAndElaborate :: Environment -> Context -> Term -> CanError (Term, Term)
inferTypeAndElaborate env ctx m = do
  result <- runInferType initContexts initState m
  msol   <- solveConstraints env ctx (mctx $ snd result) (mcsts $ snd result)
  let ts = fst result
  let e  = expandMetas msol $ fst ts
  let t  = expandMetas msol $ snd ts
  return (e, t)
  where
    initContexts = Contexts { env=env, ctx=ctx, bctx=[], tbctx=[] }
    initState    = MetaState { mcsts=[], mctx=[], metaID=0 }

inferType :: Environment -> Context -> Term -> CanError Term
inferType env ctx m = do
  (_, mt) <- inferTypeAndElaborate env ctx m
  
  return mt

elaborate :: Environment -> Context -> Term -> CanError Term
elaborate env ctx m = do
  (em, _) <- inferTypeAndElaborate env ctx m
  
  return em

checkTypeAndElaborate :: Environment-> Context -> Term -> Term -> CanError (Term, Term)
checkTypeAndElaborate env ctx m t = do
  result <- runCheckType initContexts initState m $ eval $ resolve env t
  msol   <- solveConstraints env ctx (mctx $ snd result) (mcsts $ snd result)
  let ts = fst result
  let e  = expandMetas msol $ fst ts
  let t  = expandMetas msol $ snd ts
  return (e, t)
  where
    initContexts = Contexts { env=env, ctx=ctx, bctx=[], tbctx=[] }
    initState    = MetaState { mcsts=[], mctx=[], metaID=0 }

checkType :: Environment -> Context -> Term -> Term -> CanError Term
checkType env ctx m t = do
  (_, mt) <- checkTypeAndElaborate env ctx m t
  
  return mt

elaborateWithType :: Environment -> Context -> Term -> Term -> CanError Term
elaborateWithType env ctx m t = do
  (em, _) <- checkTypeAndElaborate env ctx m t
  
  return em
