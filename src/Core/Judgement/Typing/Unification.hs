module Core.Judgement.Typing.Unification where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation
import Core.Judgement.Typing.Context
import Core.Judgement.Typing.Inference

import GHC.Base (when)
import Data.Maybe (fromMaybe)
import Control.Monad (unless)
import Data.List (elemIndex)
import Data.Bifunctor (second)
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.ByteString.Lazy.Char8 (pack)

type MetaSolution  = (Int, Term)
type MetaSolutions = [MetaSolution]

data UniState = UniState
  { sols  :: MetaSolutions
  , csts  :: Constraints
  }

data UniContexts = UniContexts
  { uenv :: Environment
  , uctx :: Context
  , umctx :: MetaContext
  }

type Unification a = ReaderT UniContexts (StateT UniState CanError) a

solveConstraints :: Environment -> Context -> MetaContext -> Constraints -> CanError MetaSolutions
solveConstraints env ctx mctx cs = do
  result <- execStateT (runReaderT runUnification initContexts) initState
  return $ sols result
  where
    initState    = UniState { sols=[], csts=cs }
    initContexts = UniContexts { uenv=env, uctx=ctx, umctx=mctx }

    runUnification :: Unification ()
    runUnification = do
      ctxs <- ask
      st  <- get

      -- Get constraint from worklist
      case csts st of
        []              -> return ()
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
              flexRigidSolved <- tryFlexRigidSolve et et'

              unless flexRigidSolved $ do
                -- Postpone flex-flex constraint
                appendConstraint bc t t'

          -- Loop with remaining constraints
          dropConstraint
          runUnification

    dropConstraint :: Unification ()
    dropConstraint = do
      st <- get

      case csts st of
        []     -> return ()
        (c:cs) -> do
          put $ st { csts=cs }

    tryFlexRigidSolve :: Term -> Term -> Unification Bool
    tryFlexRigidSolve m (Var (Meta i sp)) | hasRigidHead m && not (metaOccursIn i m) = do
      addSolution i sp m
      return True
    tryFlexRigidSolve (Var (Meta i sp)) t | hasRigidHead t && not (metaOccursIn i t) = tryFlexRigidSolve t $ Var $ Meta i sp
    tryFlexRigidSolve _ _                                                             = return False

    addSolution :: Int -> Spine -> Term -> Unification ()
    addSolution i sp m = do
      ctxs <- ask
      st   <- get

      let mClosed = abstractOverCtx m sp
      let allSols = (i, mClosed) : sols st

      -- Expand metas in existing solutions
      let expandedSolutions = map (second $ expandMetas allSols) $ sols st
      put $ st { sols=(i, mClosed) : expandedSolutions }
      
      case lookup i $ umctx ctxs of
        Just md -> do
          -- Create a constraint that the type of the solved meta must match the 
          -- metas expected type in the meta context
          mt <- inferSolutionType (mbctx md) $ remapCtxToSpine m sp
          appendConstraint (mbctx md) (mtype md) mt
        Nothing -> unificationError $ Just ("No expected type of " ++ show (Var $ Meta i []) ++ " found in meta context")

    inferSolutionType :: BoundContext -> Term -> Unification Term
    inferSolutionType bc m = do
      ctxs <- ask
      st   <- get

      let initContexts = Contexts { env=uenv ctxs, ctx=uctx ctxs, bctx=bc, tbctx=[] }
      -- TODO: metaID 0? No new metas *should* be created but still unsafe
      let initState    = MetaState { mcsts=csts st, mctx=umctx ctxs, metaID=0 }
      let mt = evalStateT (runReaderT (runInferType m) initContexts) initState
      
      case mt of
        Result t     -> return $ snd t
        Error errc s -> unificationError s

    abstractOverCtx :: Term -> Spine -> Term
    abstractOverCtx m sp = go 0 (remapCtxToSpine m sp) sp
      where
        go :: Int -> Term -> Spine -> Term
        go i m []     = m
        go i m (n:ns) = go (i + 1) (Lam (pack ("!m" ++ show i), Nothing, Exp) m) ns

    -- Remaps a term to the context in the provided metas spine
    remapCtxToSpine :: Term -> Spine -> Term
    remapCtxToSpine (Var (Bound i)) sp
      | Var (Bound i) `elem` sp = Var $ Bound (fromMaybe 0 $ elemIndex (Var $ Bound i) $ reverse sp)
      | otherwise               = Var $ Bound i
    remapCtxToSpine (Lam (x, Just t, ex) n) sp  = Lam (x, Just $ remapCtxToSpine t sp, ex) (remapCtxToSpine n sp)
    remapCtxToSpine (Lam (x, Nothing, ex) n) sp = Lam (x, Nothing, ex) (remapCtxToSpine n sp)
    remapCtxToSpine (Pi (x, t, ex) n) sp        = Pi (x, remapCtxToSpine t sp, ex) (remapCtxToSpine n sp)
    remapCtxToSpine (Sigma (x, t) n) sp         = Sigma (x, remapCtxToSpine t sp) (remapCtxToSpine n sp)
    remapCtxToSpine (Pair t n) sp               = Pair (remapCtxToSpine t sp) (remapCtxToSpine n sp)
    remapCtxToSpine (IdFam t) sp                = IdFam $ remapCtxToSpine t sp
    remapCtxToSpine (Id mt t n) sp              = Id (fmap (`remapCtxToSpine` sp) mt) (remapCtxToSpine t sp) (remapCtxToSpine n sp)
    remapCtxToSpine (Sum t n) sp                = Sum (remapCtxToSpine t sp) (remapCtxToSpine n sp)
    remapCtxToSpine (App t (n, ex)) sp          = App (remapCtxToSpine t sp) (remapCtxToSpine n sp, ex)
    remapCtxToSpine (Inl n) sp                  = Inl $ remapCtxToSpine n sp
    remapCtxToSpine (Inr n) sp                  = Inr $ remapCtxToSpine n sp
    remapCtxToSpine (Refl n) sp                 = Refl $ remapCtxToSpine n sp
    remapCtxToSpine (Succ n) sp                 = Succ $ remapCtxToSpine n sp
    remapCtxToSpine (Funext p) sp               = Funext $ remapCtxToSpine p sp
    remapCtxToSpine (Univalence a) sp           = Univalence $ remapCtxToSpine a sp
    remapCtxToSpine (Ind t m' c a) sp           = Ind (remapCtxToSpine t sp) (remapCtxToSpineInBoundTerm m' sp) (map (`remapCtxToSpineInBoundTerm` sp) c) (remapCtxToSpine a sp)
      where
        remapCtxToSpineInBoundTerm :: BoundTerm -> Spine -> BoundTerm
        remapCtxToSpineInBoundTerm (NoBind n) sp = NoBind (remapCtxToSpine n sp)
        remapCtxToSpineInBoundTerm (Bind x n) sp = Bind x (remapCtxToSpineInBoundTerm n sp)
    remapCtxToSpine n _                         = n

    decompose :: BoundContext -> Term -> Term -> Unification Bool
    decompose bc (Lam (x, Just t, _) m) (Lam (_, Just t', _) m') = do
      appendConstraint bc t t'
      appendConstraint ((Just x, t) : bc) m m'
      return True
    decompose bc (Lam (x, Nothing, _) m) (Lam _ m')              = do
      -- We don't know the type of x here, but need to add something
      -- to the bound context. Add Top for now (TODO?)
      appendConstraint ((Nothing, Top) : bc) m m'
      return True
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
    decompose bc (Refl m) (Refl m')                              = do
      appendConstraint bc m m'
      return True
    decompose bc (IdFam m) (IdFam m')                            = do
      appendConstraint bc m m'
      return True
    decompose bc (Ind t m cs a) (Ind t' m' cs' a')               = do
      appendConstraint bc t t'
      appendConstraintFromBoundContext bc m m'
      appendBoundConstraints bc cs cs'
      appendConstraint bc a a'
      return True
    decompose bc (Var (Meta _ _)) _                              = return False
    decompose bc _ (Var (Meta _ _))                              = return False
    decompose bc t t'                                            = do
      ctxs <- ask

      -- Try resolving terms to see if that changes them, if so try to decompose the
      -- resolved terms
      let et  = eval $ resolve (uenv ctxs) t
      let et' = eval $ resolve (uenv ctxs) t'

      if et /= t || et' /= t'
      then decompose bc et et'
      else unificationError $ Just ("Failed to unify types " ++ showTermWithContext bc t ++ " and " ++ showTermWithContext bc t')

    metaOccursIn :: Int -> Term -> Bool
    metaOccursIn k (Var (Meta i _))
      | i == k    = True
      | otherwise = False
    metaOccursIn k (Lam (x, Just t, _) n)  = metaOccursIn k t || metaOccursIn k n
    metaOccursIn k (Lam (x, Nothing, _) n) = metaOccursIn k n
    metaOccursIn k (Pi (x, t, _) n)        = metaOccursIn k t || metaOccursIn k n
    metaOccursIn k (Sigma (x, t) n)        = metaOccursIn k t || metaOccursIn k n
    metaOccursIn k (Pair t n)              = metaOccursIn k t || metaOccursIn k n
    metaOccursIn k (App t (n, _))          = metaOccursIn k t || metaOccursIn k n
    metaOccursIn k (Id mt m n)             = maybe False (metaOccursIn k) mt || metaOccursIn k m || metaOccursIn k n
    metaOccursIn k (Refl m)                = metaOccursIn k m
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
    appendConstraint bc t t' = do
      st <- get
      put $ st { csts=csts st ++ [(bc, t, t')] }

    appendBoundConstraints :: BoundContext -> [BoundTerm] -> [BoundTerm] -> Unification ()
    appendBoundConstraints _ [] []            = return ()
    appendBoundConstraints bc (c:cs) (c':cs') = do
      appendConstraintFromBoundContext bc c c'
      appendBoundConstraints bc cs cs'
    appendBoundConstraints _ _ _              = unificationError $ Just "Incompatible number of bound terms to unify"

    appendConstraintFromBoundContext :: BoundContext -> BoundTerm -> BoundTerm -> Unification ()
    appendConstraintFromBoundContext bc (NoBind m) (NoBind m') = appendConstraint bc m m'
    appendConstraintFromBoundContext bc (Bind x m) (Bind _ m') = appendConstraintFromBoundContext ((x, Top) : bc) m m'

    unificationError :: Maybe String -> Unification a
    unificationError ms = lift $ lift $ Error UnificationError ms

expandMetas :: MetaSolutions -> Term -> Term
expandMetas sols (Var (Meta i sp))        = case lookup i sols of
  Just t -> applyTermToSpine t sp
  _      -> Var (Meta i sp)
  where
    applyTermToSpine :: Term -> Spine -> Term
    applyTermToSpine m []     = m
    applyTermToSpine m (n:ns) = eval $ applyTermToSpine (App m (n, Exp)) ns
expandMetas sols (Lam (x, Just t, ex) n)  = Lam (x, Just $ expandMetas sols t, ex) (expandMetas sols n)
expandMetas sols (Lam x n)                = Lam x $ expandMetas sols n
expandMetas sols (Pi (x, t, ex) n)        = Pi (x, expandMetas sols t, ex) (expandMetas sols n)
expandMetas sols (Sigma (x, t) n)         = Sigma (x, expandMetas sols t) (expandMetas sols n)
expandMetas sols (Pair t n)               = Pair (expandMetas sols t) (expandMetas sols n)
expandMetas sols (App t (n, ex))          = App (expandMetas sols t) (expandMetas sols n, ex)
expandMetas sols (Id mt m n)              = Id (fmap (expandMetas sols) mt) (expandMetas sols m) (expandMetas sols n)
expandMetas sols (Refl m)                 = Refl $ expandMetas sols m
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
