module Core.Judgement.Typing.Unification where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation
import Core.Judgement.Typing.Context
import Core.Judgement.Typing.Inference

import Data.Set (Set)
import GHC.Base (when)
import Data.Maybe (fromMaybe)
import Control.Monad (unless)
import Data.List (elemIndex, delete, (!?))
import Data.Bifunctor (second)
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.ByteString.Lazy.Char8 (pack)
import qualified Data.Set as Set

type MetaSolution  = (Int, Term)
type MetaSolutions = [MetaSolution]

-- A blocked constraint is a constraint that is unable to be solved
-- Should any of the metas in the paired set be solved, the constraint
-- should be awoken
type BlockedConstraint  = (Constraint, Set Int)
type BlockedConstraints = [BlockedConstraint]

type Spine = [Term]

data UniState = UniState
  { sols  :: MetaSolutions
  , mst   :: MetaState
  , bcsts :: BlockedConstraints
  }

data UniContexts = UniContexts
  { uenv :: Environment
  , uctx :: Context
  }

type Unification a = ReaderT UniContexts (StateT UniState CanError) a

solveConstraints :: Environment -> Context -> MetaState -> CanError MetaSolutions
solveConstraints env ctx st = do
  result <- execStateT (runReaderT go initContexts) initState
  return $ sols result
  where
    initState    = UniState { sols=[], mst=st, bcsts=[] }
    initContexts = UniContexts { uenv=env, uctx=ctx }

    go :: Unification ()
    go = do
      ctxs <- ask
      st  <- get

      -- Get constraint from worklist
      case mcsts $ mst st of
        []              -> do
          st <- get

          -- Check if there are any blocked constraints
          if null $ bcsts st
          then return ()
          else unificationError $ Just ("Unsolved constraints" ++ show (bcsts st))
        ((bc, t, t'):_) -> do
          let et  = eval $ expandMetas (sols st) t
          let et' = eval $ expandMetas (sols st) t'

          -- Skip constraint if the two terms are definitionally equal (rigid-rigid positive case)
          unless (equal (uenv ctxs) et et') $ do
            -- Attempt to decompose constraint if terms have same rigid head
            -- (rigid-rigid negative case handled here)
            decomposed <- decompose bc et et'

            unless decomposed $ do
              -- Try to solve the flex-rigid case
              flexRigidSolved <- tryFlexRigidSolve bc et et'

              unless flexRigidSolved $ do
                -- Flex-flex constraints are blocked until one of the metas is solved
                appendBlockedConstraint bc t t'

          -- Loop with remaining constraints
          dropConstraint
          go

    dropConstraint :: Unification ()
    dropConstraint = do
      st <- get

      case mcsts $ mst st of
        []     -> return ()
        (c:cs) -> do
          put $ st { mst=(mst st) { mcsts=cs } }

    tryFlexRigidSolve :: BoundContext -> Term -> Term -> Unification Bool
    tryFlexRigidSolve bc m n
      | isFlex m && isRigid n = do
      case breakUpPattern m of
        Just (Meta i, sp) -> do
          -- Occurs check
          if metaOccursIn i n
          then return False
          else do
            -- Align indices in n to the context that the meta was created in
            let extraBinders = length bc - length sp
            sol <- abstractOverRHS 0 bc (shift (-extraBinders) n) sp
            addSolution bc i sol
            return True
        _                     -> return False
      where
        abstractOverRHS :: Int -> BoundContext -> Term -> Spine -> Unification Term
        abstractOverRHS i bc m []                 = return m
        abstractOverRHS i bc m (Var (Bound j):ns) = case bc !? j of
          Just (_, t) -> abstractOverRHS (i + 1) bc (Lam (pack ("!i" ++ show i), Just t, Exp) m) ns
          Nothing     -> unificationError $ Just "Failed to determine type of bound variable"
        abstractOverRHS _ _ _ _                   = unificationError $ Just "Constraint is not in pattern fragment"

    -- Swap terms around if in rigid-flex order
    tryFlexRigidSolve bc m n
      | isRigid m && isFlex n = tryFlexRigidSolve bc n m
    tryFlexRigidSolve _ _ _   = return False

    breakUpPattern :: Term -> Maybe (Var, Spine)
    breakUpPattern m = go m [] Set.empty
      where
        go :: Term -> Spine -> Set Int -> Maybe (Var, Spine)
        go (Var mv@(Meta i))              sp _  = return (mv, sp)
        go (App m (n@(Var (Bound i)), _)) sp bs = do
          -- Ensure that the flexible term is a metavariable applied to distinct bound variables
          if i `Set.member` bs
          then Nothing
          else go m (sp ++ [n]) (Set.insert i bs)
        -- Term is not in Miller's pattern fragment
        go _ _ _                                = Nothing

    addSolution :: BoundContext -> Int -> Term -> Unification ()
    addSolution bc i m = do
      st   <- get

      let allSols = (i, m) : sols st

      -- Expand metas in existing solutions
      let expandedSolutions = map (second $ expandMetas allSols) $ sols st
      put $ st { sols=(i, m) : expandedSolutions }

      -- Wake up blocked constraints that are awaiting this metas solution
      wakeUpBlockedConstraints i

      case lookup i $ mctx $ mst st of
        Just md -> do
          -- Create a constraint that the type of the solved meta must match its expected type
          -- No context is needed since metas are all closed terms
          mt <- inferSolutionType [] m
          appendConstraint [] (mtype md) mt
        Nothing -> unificationError $ Just ("No expected type of " ++ show (Var $ Meta i) ++ " found in meta context")

    wakeUpBlockedConstraints :: Int -> Unification ()
    wakeUpBlockedConstraints i = do
      st <- get
      mapM_  (wakeUpBlockedConstraint i) $ bcsts st
      where
        wakeUpBlockedConstraint :: Int -> BlockedConstraint -> Unification ()
        wakeUpBlockedConstraint i bc@(c, s) = do
          when (i `Set.member` s) $ do
            st <- get

            let newBcsts = delete bc $ bcsts st
            let newCsts = mcsts (mst st) ++ [c]
            put $ st { mst=(mst st) { mcsts=newCsts }, bcsts=newBcsts }

    inferSolutionType :: BoundContext -> Term -> Unification Term
    inferSolutionType bc m = do
      ctxs <- ask
      st   <- get

      let initContexts = Contexts { env=uenv ctxs, ctx=uctx ctxs, bctx=bc, tbctx=[] }
      let mt = evalInferType initContexts (mst st) m

      case mt of
        Result t     -> return $ snd t
        Error errc s -> unificationError s

    decompose :: BoundContext -> Term -> Term -> Unification Bool
    -- Flex-flex case
    decompose _ m m' | isFlex m && isFlex m'                     = return False
    -- Flex-rigid case
    decompose _ m m' | isFlex m /= isFlex m'                     = return False
    -- Rigid-rigid cases
    decompose bc (Lam (x, Just t, _) m) (Lam (_, Just t', _) m') = do
      appendConstraint bc t t'
      appendConstraint ((Just x, t) : bc) m m'
      return True
    decompose bc (Lam (x, Nothing, _) m) (Lam _ m')              = do
      unificationError $ Just "Unable to decompose implicit lambda for unification"
    decompose bc (Pi (x, t, _) m) (Pi (_, t', _) m')             = do
      appendConstraint bc t t'
      appendConstraint ((x, t) : bc) m m'
      return True
    decompose bc (Sigma (x, t) m) (Sigma (_, t') m')             = do
      appendConstraint bc t t'
      appendConstraint ((x, t) : bc) m m'
      return True
    decompose bc (Id (Just t) m n) (Id (Just t') m' n')          = do
      appendConstraint bc t t'
      appendConstraint bc m m'
      appendConstraint bc n n'
      return True
    decompose bc (Id _ m n) (Id _ m' n')                         = do
      appendConstraint bc m m'
      appendConstraint bc n n'
      return True
    decompose bc (App m (n, _)) (App m' (n', _))                 = do
      appendConstraint bc m m'
      appendConstraint bc n n'
      return True
    decompose bc (Pair m n) (Pair m' n')                         = do
      appendConstraint bc m m'
      appendConstraint bc n n'
      return True
    decompose bc (Sum m n) (Sum m' n')                           = do
      appendConstraint bc m m'
      appendConstraint bc n n'
      return True
    decompose bc (Succ m) (Succ m')                              = do
      appendConstraint bc m m'
      return True
    decompose bc (Inl m) (Inl m')                                = do
      appendConstraint bc m m'
      return True
    decompose bc (Inr m) (Inr m')                                = do
      appendConstraint bc m m'
      return True
    decompose bc (Funext m) (Funext m')                          = do
      appendConstraint bc m m'
      return True
    decompose bc (Univalence m) (Univalence m')                  = do
      appendConstraint bc m m'
      return True
    decompose bc (Refl (Just m)) (Refl (Just m'))                = do
      appendConstraint bc m m'
      return True
    decompose bc (IdFam m) (IdFam m')                            = do
      appendConstraint bc m m'
      return True
    decompose bc (Ind t m cs a) (Ind t' m' cs' a')               = do
      appendConstraint bc t t'
      appendBoundTermConstraint bc m m'
      appendBoundTermConstraints bc cs cs'
      appendConstraint bc a a'
      return True
    decompose bc m m'                                            = do
      ctxs <- ask

      -- Try fully unfolding terms
      let em  = eval $ unfold (uenv ctxs) m
      let em' = eval $ unfold (uenv ctxs) m'

      if em /= m || em' /= m'
      then decompose bc em em'
      else unificationError $ Just ("Failed to unify " ++ showTermWithContext bc m ++ " and " ++ showTermWithContext bc m')

    metaOccursIn :: Int -> Term -> Bool
    metaOccursIn k (Var (Meta i))
      | i == k    = True
      | otherwise = False
    metaOccursIn k (Lam (x, Just t, _) n)  = metaOccursIn k t || metaOccursIn k n
    metaOccursIn k (Lam (x, Nothing, _) n) = metaOccursIn k n
    metaOccursIn k (Pi (x, t, _) n)        = metaOccursIn k t || metaOccursIn k n
    metaOccursIn k (Sigma (x, t) n)        = metaOccursIn k t || metaOccursIn k n
    metaOccursIn k (Pair t n)              = metaOccursIn k t || metaOccursIn k n
    metaOccursIn k (App t (n, _))          = metaOccursIn k t || metaOccursIn k n
    metaOccursIn k (Id mt m n)             = maybe False (metaOccursIn k) mt || metaOccursIn k m || metaOccursIn k n
    metaOccursIn k (Refl m)                = maybe False (metaOccursIn k) m
    metaOccursIn k (Funext m)              = metaOccursIn k m
    metaOccursIn k (Univalence m)          = metaOccursIn k m
    metaOccursIn k (Succ m)                = metaOccursIn k m
    metaOccursIn k (Inl m)                 = metaOccursIn k m
    metaOccursIn k (Inr m)                 = metaOccursIn k m
    metaOccursIn k (IdFam m)               = metaOccursIn k m
    metaOccursIn k (Ind t m' c a)          = metaOccursIn k t || metaOccursInBoundTerm k m' || any (metaOccursInBoundTerm k) c || metaOccursIn k a
      where
        metaOccursInBoundTerm k (NoBind n) = metaOccursIn k n
        metaOccursInBoundTerm k (Bind x n) = metaOccursInBoundTerm k n
    metaOccursIn k n                       = False

    appendConstraint :: BoundContext -> Term -> Term -> Unification ()
    appendConstraint bc m m' = do
      st <- get
      put $ st { mst=(mst st) { mcsts=mcsts (mst st) ++ [(bc, m, m')] } }

    appendBlockedConstraint :: BoundContext -> Term -> Term -> Unification ()
    appendBlockedConstraint bc m m' = do
      st <- get
      put $ st { bcsts=bcsts st ++ [((bc, m, m'), getMetasInTerm m <> getMetasInTerm m')] }

    appendBoundTermConstraints :: BoundContext -> [BoundTerm] -> [BoundTerm] -> Unification ()
    appendBoundTermConstraints _ [] []            = return ()
    appendBoundTermConstraints bc (c:cs) (c':cs') = do
      appendBoundTermConstraint bc c c'
      appendBoundTermConstraints bc cs cs'
    appendBoundTermConstraints _ _ _              = unificationError $ Just "Incompatible number of bound terms to unify"

    appendBoundTermConstraint :: BoundContext -> BoundTerm -> BoundTerm -> Unification ()
    appendBoundTermConstraint bc (NoBind m) (NoBind m') = appendConstraint bc m m'
    -- We don't know the type of x here, but need to add something
    -- to the bound context. Add Top for now (TODO?)
    appendBoundTermConstraint bc (Bind x m) (Bind _ m') = appendBoundTermConstraint ((x, Top) : bc) m m'

    unificationError :: Maybe String -> Unification a
    unificationError ms = lift $ lift $ Error UnificationError ms

expandMetas :: MetaSolutions -> Term -> Term
expandMetas sols (Var (Meta i))           = case lookup i sols of
  Just t -> t
  _      -> Var (Meta i)
expandMetas sols (Lam (x, Just t, ex) n)  = Lam (x, Just $ expandMetas sols t, ex) (expandMetas sols n)
expandMetas sols (Lam x n)                = Lam x $ expandMetas sols n
expandMetas sols (Pi (x, t, ex) n)        = Pi (x, expandMetas sols t, ex) (expandMetas sols n)
expandMetas sols (Sigma (x, t) n)         = Sigma (x, expandMetas sols t) (expandMetas sols n)
expandMetas sols (Pair t n)               = Pair (expandMetas sols t) (expandMetas sols n)
expandMetas sols (App t (n, ex))          = App (expandMetas sols t) (expandMetas sols n, ex)
expandMetas sols (Id mt m n)              = Id (fmap (expandMetas sols) mt) (expandMetas sols m) (expandMetas sols n)
expandMetas sols (Refl m)                 = Refl $ fmap (expandMetas sols) m
expandMetas sols (Funext m)               = Funext $ expandMetas sols m
expandMetas sols (Univalence m)           = Univalence $ expandMetas sols m
expandMetas sols (Succ m)                 = Succ $ expandMetas sols m
expandMetas sols (Inl m)                  = Inl $ expandMetas sols m
expandMetas sols (Inr m)                  = Inr $ expandMetas sols m
expandMetas sols (IdFam m)                = IdFam $ expandMetas sols m
expandMetas sols (Ind t m' c a)           = Ind (expandMetas sols t) (expandMetasInBoundTerm sols m') (map (expandMetasInBoundTerm sols) c) (expandMetas sols a)
  where
    expandMetasInBoundTerm :: MetaSolutions -> BoundTerm -> BoundTerm
    expandMetasInBoundTerm sols (NoBind m) = NoBind $ expandMetas sols m
    expandMetasInBoundTerm sols (Bind x m) = Bind x $ expandMetasInBoundTerm sols m
expandMetas sols m                        = m
