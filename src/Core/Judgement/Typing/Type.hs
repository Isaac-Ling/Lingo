module Core.Judgement.Typing.Type where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation
import Core.Judgement.Context
import Core.Judgement.Typing.Universe
import Core.Judgement.Typing.Inference
import Core.Judgement.Typing.Unification

import Data.Set (Set)
import Control.Monad (when)
import qualified Data.Set as Set

data TypingResult = TypingResult
  { tterm :: Term
  , ttype :: Term
  , tcsts :: UnivConstraints
  }

inferTypeAndElaborate :: Environment -> Context -> Term -> CanError TypingResult
inferTypeAndElaborate env ctx m = do
  let mUData    = instantiateUnivs m 0
  let initState = TypeCheckState { mcsts=[], ucsts=[], mctx=[], metaID=0, univID=fuid mUData }
  result <- runInferType initContexts initState $ uterm mUData
  msol   <- solveMetaConstraints env ctx $ snd result
  let ts = fst result
  let e  = expandMetas msol $ fst ts
  let t  = expandMetas msol $ snd ts

  when (containsMeta e || containsMeta t) $
    Error FailedToInferType $ Just "Unsolved meta variable(s) remaining"

  checkUnivConstraintsSatisfiable $ ucsts $ snd result
  let univConstraints = filterConstraints e $ ucsts $ snd result

  return TypingResult {tterm=e, ttype=t, tcsts=univConstraints}
  where
    initContexts = Contexts { env=env, ctx=ctx, bctx=[], tbctx=[] }

inferType :: Environment -> Context -> Term -> CanError Term
inferType env ctx m = do
  tr <- inferTypeAndElaborate env ctx m
  
  return $ ttype tr

elaborate :: Environment -> Context -> Term -> CanError Term
elaborate env ctx m = do
  tr <- inferTypeAndElaborate env ctx m
  
  return $ tterm tr

checkTypeAndElaborate :: Environment-> Context -> Term -> Term -> CanError TypingResult
checkTypeAndElaborate env ctx m t = do
  let mUData    = instantiateUnivs m 0
  let tUData    = instantiateUnivs t $ fuid mUData
  let initState = TypeCheckState { mcsts=[], ucsts=[], mctx=[], metaID=0, univID=fuid tUData }
  result <- runCheckType initContexts initState (uterm mUData) $ eval $ unfold env (uterm tUData)
  msol   <- solveMetaConstraints env ctx $ snd result
  let ts = fst result
  let e  = expandMetas msol $ fst ts
  let t  = expandMetas msol $ snd ts

  when (containsMeta e || containsMeta t) $
    Error FailedToInferType $ Just "Unsolved meta variable(s) remaining"

  checkUnivConstraintsSatisfiable $ ucsts $ snd result
  let univConstraints = filterConstraints e $ ucsts $ snd result

  return TypingResult {tterm=e, ttype=t, tcsts=univConstraints}
  where
    initContexts = Contexts { env=env, ctx=ctx, bctx=[], tbctx=[] }

checkType :: Environment -> Context -> Term -> Term -> CanError Term
checkType env ctx m t = do
  tr <- checkTypeAndElaborate env ctx m t
  
  return $ ttype tr

elaborateWithType :: Environment -> Context -> Term -> Term -> CanError Term
elaborateWithType env ctx m t = do
  tr <- checkTypeAndElaborate env ctx m t
  
  return $ tterm tr

filterConstraints :: Term -> UnivConstraints -> UnivConstraints
filterConstraints m = filter (areVarsInConstraint uVars)
  where
    areVarsInConstraint :: Set Int -> UnivConstraint -> Bool
    areVarsInConstraint vs (ULeq u v) = areUnivsInSet vs u v
    areVarsInConstraint vs (ULt u v)  = areUnivsInSet vs u v

    areUnivsInSet :: Set Int -> Universe -> Universe -> Bool
    areUnivsInSet vs u v = case (getIDFromUniv u, getIDFromUniv v) of
      (Just i, Just j) -> i `Set.member` vs && j `Set.member` vs
      (Just i, _     ) -> i `Set.member` vs
      (_     , Just j) -> j `Set.member` vs
      (_     , _     ) -> False

    getIDFromUniv :: Universe -> Maybe Int
    getIDFromUniv (UVar i) = Just i
    getIDFromUniv _        = Nothing

    uVars :: Set Int
    uVars = getUnivVarsInTerm m
