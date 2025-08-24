module Core.Judgement.Typing.Unification where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation
import Core.Judgement.Typing.Context

import Control.Monad (unless)
import Data.Maybe (fromMaybe)
import Control.Monad.Reader
import Control.Monad.State.Lazy
import GHC.Base (when)

type MetaSolution  = (Int, Maybe Term)
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
    put st { csts=cst : csts st }

type Unification = ReaderT Environment (StateT MetaSolutions CanError) ()

solveConstraints :: Environment -> Constraints -> CanError MetaSolutions
solveConstraints env cs = execStateT (runReaderT (go cs) env) []
  where
    go :: Constraints -> Unification
    go []                 = return ()
    go ((bc, t, t'):csts) = do
      env  <- ask
      sols <- get
      
      let et  = eval $ expandMetas sols t
      let et' = eval $ expandMetas sols t'

      -- Drop constraint if the two terms are definitionally equal
      when (equal env et et') $
        go cs

      -- Decompose goals if terms have same rigid head
      decompose bc t t'

    decompose :: BoundContext -> Term -> Term -> Unification
    decompose bc (App (Var (Meta _)) _) _ = return ()
    decompose bc _ (App (Var (Meta _)) _) = return ()
    decompose bc (Var (Meta _)) _         = return ()
    decompose bc _ (Var (Meta _))         = return ()
    decompose bc t t'                     = unificationError $ Just ("Failed to unify types " ++ showTermWithContext bc t ++ " and " ++ showTermWithContext bc t')

    unificationError :: Maybe String -> Unification
    unificationError ms = lift $ lift $ Error UnificationError ms

  {-
  case solveConstraint (bc, t, t') of
    Just sol -> do
      sols <- solveConstraints cs
      return $ sol : sols
    _        -> 
  -}

solveConstraint :: Constraint -> Maybe MetaSolution
solveConstraint (_, m, Var (Meta i)) = Just (i, Just m)
solveConstraint (_, Var (Meta i), m) = Just (i, Just m)
solveConstraint _                    = Nothing

-- TODO: Manage contexts when moving in binders
expandMetas :: MetaSolutions -> Term -> Term
expandMetas sols (Var (Meta i))           = case lookup i sols of
  Just (Just t) -> t
  _             -> Var (Meta i)
expandMetas sols (Lam (x, Just t, ex) n)  = Lam (x, Just $ expandMetas sols t, ex) (expandMetas sols n)
expandMetas sols (Lam x n)                = Lam x $ expandMetas sols n
expandMetas sols (Pi (x, t, ex) n)        = Pi (x, expandMetas sols t, ex) (expandMetas sols n)
expandMetas sols (Sigma (x, t) n)         = Sigma (x, expandMetas sols t) (expandMetas sols n)
expandMetas sols (Pair t n)               = Pair (expandMetas sols t) (expandMetas sols n)
expandMetas sols (App t n)                = App (expandMetas sols t) (expandMetas sols n)
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
    expandMetasInBoundTerm sols (Bind _ m) = expandMetasInBoundTerm sols m
expandMetas sols m                        = m
