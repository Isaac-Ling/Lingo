module Core.Judgement.Typing.Unification where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation
import Core.Judgement.Typing.Context

import GHC.Base (when)
import Control.Monad (unless)
import Data.Maybe (fromMaybe)
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.ByteString.Lazy.Char8 (empty)

type MetaSolution  = (Int, Term)
type MetaSolutions = [MetaSolution]

unify :: Term -> Term -> Maybe String -> TypeCheck ()
unify t t' ms = do
  ctxs <- ask
  let errorString = fromMaybe ("Failed to unify types " ++ showTermWithContext (bctx ctxs) t ++ " and " ++ showTermWithContext (bctx ctxs) t') ms

  if isRigid t && isRigid t'
  then unless (equal (env ctxs) t t') $
    typeError TypeMismatch $ Just errorString
  else do
    -- Add constraint
    st <- get
    let cst = (bctx ctxs, t, t')
    put st { mcsts=cst : mcsts st }

data UniState = UniState
  { sols :: MetaSolutions
  , csts :: Constraints
  }

type Unification a = ReaderT Environment (StateT UniState CanError) a

solveConstraints :: Environment -> Constraints -> CanError MetaSolutions
solveConstraints env cs = do
  result <- runStateT (runReaderT runUnification env) initState
  return $ sols $ snd result
  where
    initState   = UniState { sols=[], csts=cs }

    runUnification :: Unification ()
    runUnification = do
      env <- ask
      st  <- get

      -- Get constraint from worklist
      case csts st of
        []              -> return ()
        ((bc, t, t'):_) -> do
          let et  = eval $ expandMetas (sols st) t
          let et' = eval $ expandMetas (sols st) t'

          -- Skip constraint if the two terms are definitionally equal
          unless (equal env et et') $ do
            -- Attempt to decompose constraint if terms have same rigid head
            decomposed <- decompose bc et et'

            unless decomposed $
              tryTrivialSolve et et'

              -- TODO: Solve non-trivial cases
      
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

    tryTrivialSolve :: Term -> Term -> Unification ()
    tryTrivialSolve t (Var (Meta i sp)) = do
      when (isRigid t) $ do
        addSolution i $ abstractOverCtx t sp
    tryTrivialSolve (Var (Meta i sp)) t = do
      when (isRigid t) $ do
        addSolution i $ abstractOverCtx t sp
    -- TODO: Trivial solve meta applied to a list of args

    abstractOverCtx :: Term -> [Term] -> Term
    abstractOverCtx m []     = m
    abstractOverCtx m (n:ns) = abstractOverCtx (Lam (empty, Nothing, Exp) m) ns

    addSolution :: Int -> Term -> Unification ()
    addSolution i m = do
      st <- get
      put $ st { sols=(i, m) : sols st }

    decompose :: BoundContext -> Term -> Term -> Unification Bool
    decompose bc (Lam (x, Just t, _) m) (Lam (_, Just t', _) m') = do
      appendConstraint bc t t'
      appendConstraint ((Just x, t) : bc) m m'
      return True
    decompose bc (Lam _ m) (Lam _ m')                            = do
      appendConstraint bc m m'
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
    decompose bc (App (Var (Meta _ _)) _) _                      = return False
    decompose bc _ (App (Var (Meta _ _)) _)                      = return False
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
    -- TODO: Decompose induction
    decompose bc (Var (Meta _ _)) _                              = return False
    decompose bc _ (Var (Meta _ _))                              = return False
    decompose bc t t'                                            = unificationError $ Just ("Failed to unify types " ++ showTermWithContext bc t ++ " and " ++ showTermWithContext bc t')

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

    unificationError :: Maybe String -> Unification a
    unificationError ms = lift $ lift $ Error UnificationError ms

expandMetas :: MetaSolutions -> Term -> Term
expandMetas sols (Var (Meta i sp))        = case lookup i sols of
  Just t -> applyTermToSpine t sp
  _      -> Var (Meta i sp)
  where
    applyTermToSpine :: Term -> [Term] -> Term
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
