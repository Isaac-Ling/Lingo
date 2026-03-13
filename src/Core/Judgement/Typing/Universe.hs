module Core.Judgement.Typing.Universe where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Context

import Data.Set (Set)
import Control.Monad.State.Lazy
import qualified Data.Set as Set

checkUnivConstraintsSatisfiable :: UnivConstraints -> CanError ()
checkUnivConstraintsSatisfiable csts = case csts of
  [] -> return ()
  _  -> return ()

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

type InsUniv a = State (Int, UnivSub) a
type UnivSub   = [(Universe, Universe)]

data UnivData = UnivData
  { uterm :: Term
  , fuid  :: Int
  , usub  :: UnivSub
  }

applySubToConstraints :: UnivSub -> UnivConstraints -> UnivConstraints
applySubToConstraints sub []            = []
applySubToConstraints sub (ULeq u v:cs) = ULeq (applySubToUniverse sub u) (applySubToUniverse sub v) : applySubToConstraints sub cs
applySubToConstraints sub (ULt u v:cs)  = ULt (applySubToUniverse sub u) (applySubToUniverse sub v) : applySubToConstraints sub cs

applySubToUniverse :: UnivSub -> Universe -> Universe
applySubToUniverse sub u = case lookup u sub of
  Just v -> v
  _      -> u

instantiateUnivs :: Term -> Int -> UnivData
instantiateUnivs m i = udata
  where
    result = runState (go m) (i, [])
    udata  = UnivData { uterm=fst result, fuid=fst $ snd result, usub=snd $ snd result }

    go :: Term -> InsUniv Term
    go (Univ UFlex)             = do
      (univID, sub) <- get
      put (univID + 1, sub)
      return $ Univ $ UVar univID
    go (Univ (UParam i))        = do
      (univID, sub) <- get
      put (univID + 1, (UParam i, UVar univID) : sub)
      return $ Univ $ UVar univID
    go (Lam (x, Nothing, ex) m) = do
      m' <- go m
      return $ Lam (x, Nothing, ex) m'
    go (Lam (x, Just t, ex) m)  = do
      t' <- go t
      m' <- go m
      return $ Lam (x, Just t', ex) m'
    go (Pi (x, t, ex) m)        = do
      t' <- go t
      m' <- go m
      return $ Pi (x, t', ex) m'
    go (Sigma (x, t) m)         = do
      t' <- go t
      m' <- go m
      return $ Sigma (x, t') m'
    go (App m (n, ex))          = do
      m' <- go m
      n' <- go n
      return $ App m' (n', ex)
    go (Pair m n)               = do
      m' <- go m
      n' <- go n
      return $ Pair m' n'
    go (Sum m n)                = do
      m' <- go m
      n' <- go n
      return $ Sum m' n'
    go (IdFam t)                = do
      t' <- go t
      return $ IdFam t'
    go (Id t m n)               = do
      t' <- traverse go t
      m' <- go m
      n' <- go n
      return $ Id t' m' n'
    go (Ind t m c a)            = do
      t' <- go t
      m' <- instantiateUnivsInBoundTerm m
      c' <- traverse instantiateUnivsInBoundTerm c
      a' <- go a
      return $ Ind t' m' c' a'
    go (Succ m)                 = Succ <$> go m
    go (Inl m)                  = Inl <$> go m
    go (Inr m)                  = Inr <$> go m
    go (Funext p)               = Funext <$> go p
    go (Univalence f)           = Univalence <$> go f
    go (Refl m)                 = do
      m' <- traverse go m
      return $ Refl m'
    go m                        = return m

    instantiateUnivsInBoundTerm :: BoundTerm -> InsUniv BoundTerm
    instantiateUnivsInBoundTerm (NoBind m) = NoBind <$> go m
    instantiateUnivsInBoundTerm (Bind x m) = Bind x <$> instantiateUnivsInBoundTerm m

univVarsToParams :: Term -> UnivData
univVarsToParams m = udata
  where
    result = runState (go m) (0, [])
    udata  = UnivData { uterm=fst result, fuid=fst $ snd result, usub=snd $ snd result }

    go :: Term -> InsUniv Term
    go (Univ (UVar i))          = do
      (univID, sub) <- get
      put (univID + 1, (UVar i, UParam univID) : sub)
      return $ Univ $ UParam univID
    go (Lam (x, Nothing, ex) m) = do
      m' <- go m
      return $ Lam (x, Nothing, ex) m'
    go (Lam (x, Just t, ex) m)  = do
      t' <- go t
      m' <- go m
      return $ Lam (x, Just t', ex) m'
    go (Pi (x, t, ex) m)        = do
      t' <- go t
      m' <- go m
      return $ Pi (x, t', ex) m'
    go (Sigma (x, t) m)         = do
      t' <- go t
      m' <- go m
      return $ Sigma (x, t') m'
    go (App m (n, ex))          = do
      m' <- go m
      n' <- go n
      return $ App m' (n', ex)
    go (Pair m n)               = do
      m' <- go m
      n' <- go n
      return $ Pair m' n'
    go (Sum m n)                = do
      m' <- go m
      n' <- go n
      return $ Sum m' n'
    go (IdFam t)                = do
      t' <- go t
      return $ IdFam t'
    go (Id t m n)               = do
      t' <- traverse go t
      m' <- go m
      n' <- go n
      return $ Id t' m' n'
    go (Ind t m c a)            = do
      t' <- go t
      m' <- univVarsToParamsInBoundTerm m
      c' <- traverse univVarsToParamsInBoundTerm c
      a' <- go a
      return $ Ind t' m' c' a'
    go (Succ m)                 = Succ <$> go m
    go (Inl m)                  = Inl <$> go m
    go (Inr m)                  = Inr <$> go m
    go (Funext p)               = Funext <$> go p
    go (Univalence f)           = Univalence <$> go f
    go (Refl m)                 = do
      m' <- traverse go m
      return $ Refl m'
    go m                        = return m

    univVarsToParamsInBoundTerm :: BoundTerm -> InsUniv BoundTerm
    univVarsToParamsInBoundTerm (NoBind m) = NoBind <$> go m
    univVarsToParamsInBoundTerm (Bind x m) = Bind x <$> univVarsToParamsInBoundTerm m
