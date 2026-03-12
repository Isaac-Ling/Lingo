module Core.Judgement.Typing.Type where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation
import Core.Judgement.Typing.Context
import Core.Judgement.Typing.Inference
import Core.Judgement.Typing.Unification

import Control.Monad (when)
import Control.Monad.State.Lazy

inferTypeAndElaborate :: Environment -> Context -> Term -> CanError (Term, Term)
inferTypeAndElaborate env ctx m = do
  let (m', univID) = instantiateFlexUnivs m 0
  let initState    = TypeCheckState { mcsts=[], ucsts=[], mctx=[], metaID=0, univID=univID, univPID=0 }
  result <- runInferType initContexts initState m'
  msol   <- solveConstraints env ctx $ snd result
  let ts = fst result
  let e  = expandMetas msol $ fst ts
  let t  = expandMetas msol $ snd ts

  when (containsMeta e || containsMeta t) $
    Error FailedToInferType $ Just "Unsolved meta variable(s) remaining"

  return (e, t)
  where
    initContexts = Contexts { env=env, ctx=ctx, bctx=[], tbctx=[] }

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
  let (m', univID) = instantiateFlexUnivs m 0
  let (t', univID') = instantiateFlexUnivs t univID
  let initState    = TypeCheckState { mcsts=[], ucsts=[], mctx=[], metaID=0, univID=univID', univPID=0 }
  result <- runCheckType initContexts initState m' $ eval $ unfold env t'
  msol   <- solveConstraints env ctx $ snd result
  let ts = fst result
  let e  = expandMetas msol $ fst ts
  let t  = expandMetas msol $ snd ts

  when (containsMeta e || containsMeta t) $
    Error FailedToInferType $ Just "Unsolved meta variable(s) remaining"

  return (e, t)
  where
    initContexts = Contexts { env=env, ctx=ctx, bctx=[], tbctx=[] }

checkType :: Environment -> Context -> Term -> Term -> CanError Term
checkType env ctx m t = do
  (_, mt) <- checkTypeAndElaborate env ctx m t
  
  return mt

elaborateWithType :: Environment -> Context -> Term -> Term -> CanError Term
elaborateWithType env ctx m t = do
  (em, _) <- checkTypeAndElaborate env ctx m t
  
  return em

type InsUniv a = State Int a

instantiateFlexUnivs :: Term -> Int -> (Term, Int)
instantiateFlexUnivs m = runState (go m)
  where
    go :: Term -> InsUniv Term
    go (Univ UFlex)                   = do
      univID <- get
      put $ univID + 1
      return $ Univ $ UMeta univID
    go (Lam (x, Nothing, ex) m)        = do
      m' <- go m
      return $ Lam (x, Nothing, ex) m'
    go (Lam (x, Just t, ex) m)         = do
      t' <- go t
      m' <- go m
      return $ Lam (x, Just t', ex) m'
    go (Pi (x, t, ex) m)               = do
      t' <- go t
      m' <- go m
      return $ Pi (x, t', ex) m'
    go (Sigma (x, t) m)                = do
      t' <- go t
      m' <- go m
      return $ Sigma (x, t') m'
    go (App m (n, ex))                 = do
      m' <- go m
      n' <- go n
      return $ App m' (n', ex)
    go (Pair m n)                      = do
      m' <- go m
      n' <- go n
      return $ Pair m' n'
    go (Sum m n)                       = do
      m' <- go m
      n' <- go n
      return $ Sum m' n'
    go (IdFam t)                       = do
      t' <- go t
      return $ IdFam t'
    go (Id t m n)                      = do
      t' <- traverse go t
      m' <- go m
      n' <- go n
      return $ Id t' m' n'
    go (Ind t m c a)                   = do
      t' <- go t
      m' <- boundTermToCoreTerm m
      c' <- traverse boundTermToCoreTerm c
      a' <- go a
      return $ Ind t' m' c' a'
    go (Succ m)                        = Succ <$> go m
    go (Inl m)                         = Inl <$> go m
    go (Inr m)                         = Inr <$> go m
    go (Funext p)                      = Funext <$> go p
    go (Univalence f)                  = Univalence <$> go f
    go (Refl m)                        = do
      m' <- traverse go m
      return $ Refl m'
    go m                               = return m

    boundTermToCoreTerm :: BoundTerm -> InsUniv BoundTerm
    boundTermToCoreTerm (NoBind m) = NoBind <$> go m
    boundTermToCoreTerm (Bind x m) = Bind x <$> boundTermToCoreTerm m
