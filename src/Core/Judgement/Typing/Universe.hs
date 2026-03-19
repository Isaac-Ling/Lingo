module Core.Judgement.Typing.Universe where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Context

import Data.Set (Set)
import Data.Map (Map)
import Data.List (nub)
import Control.Monad (when)
import Control.Monad.State.Lazy
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

data BFNode
  = BFVar Int
  | BFNum Int
  deriving (Eq, Show, Ord)

data BFEdge = BFEdge
  { source :: BFNode
  , target :: BFNode
  , weight :: Int
  } deriving Show

data Distance
  = Fin Int
  | Inf
  deriving (Eq, Show)

type BFGraph = [BFEdge]
type Dist    = Map BFNode Distance

checkUnivConstraintsSatisfiable :: UnivConstraints -> CanError ()
checkUnivConstraintsSatisfiable csts = do
  g' <- toBFGraph csts
  let g = addNumEdges $ addSource g'
  let d = bellmanFord g

  when (hasNegativeCycle d g) $
    Error UniverseError $ Just "Universe constraints unsatisfiable"
  where
    toBFNode :: Universe -> CanError BFNode
    toBFNode (UVar i) = return $ BFVar i
    toBFNode (ULvl i) = return $ BFNum i
    toBFNode u        = Error UniverseError $ Just ("Invalid universe " ++ show u ++ " for satisfiability check")

    toBFEdge :: UnivConstraint -> CanError BFEdge
    toBFEdge (ULeq u v) = do
      ut  <- toBFNode u
      vt  <- toBFNode v
      -- u - v <= 0
      return BFEdge { source=vt, target=ut, weight=0 }
    toBFEdge (ULt u v)  = do
      ut  <- toBFNode u
      vt  <- toBFNode v
      -- u - v <= -1
      return BFEdge { source=vt, target=ut, weight= -1 }

    toBFGraph :: UnivConstraints -> CanError BFGraph
    toBFGraph = traverse toBFEdge

    getNodes :: BFGraph -> [BFNode]
    getNodes = nub . concatMap getNodesFromEdge
      where
        getNodesFromEdge :: BFEdge -> [BFNode]
        getNodesFromEdge e = [source e, target e]

    s :: BFNode
    s = BFVar (-1)

    initDist :: [BFNode] -> Dist
    initDist ns = Map.fromList $ (s, Fin 0) : [(n, Inf) | n <- ns, n /= s]

    getNums :: BFGraph -> [Int]
    getNums g = [ i | BFNum i <- getNodes g ]

    -- Add edges to constrain distances to constant numeric nodes
    addNumEdges :: BFGraph -> BFGraph
    addNumEdges g = concatMap makeNumEdges is ++ g
      where
        is = getNums g

        makeNumEdges :: Int -> [BFEdge]
        makeNumEdges i = 
          [ BFEdge { source=s, target=BFNum i, weight=i }
          , BFEdge { source=BFNum i, target=s, weight= -i }
          ]

    addSource :: BFGraph -> BFGraph
    addSource g = [BFEdge { source=s, target=n, weight=0 } | n <- getNodes g] ++ g

    du :: Dist -> BFEdge -> Distance
    du d e = Map.findWithDefault Inf (source e) d

    dv :: Dist -> BFEdge -> Distance
    dv d e = Map.findWithDefault Inf (target e) d

    -- Relax constraints |g| - 1 times
    bellmanFord :: BFGraph -> Dist
    bellmanFord g = iterate (relaxGraph g) d !! length ns
      where
        ns = getNodes g
        d  = initDist ns

    relax :: Dist -> BFEdge -> Dist
    relax d e = case (du d e, dv d e) of
      (Fin u, Fin v) -> if v > u + w
        then Map.insert (target e) (Fin $ u + w) d
        else d
      (Fin u, Inf)   -> Map.insert (target e) (Fin $ u + w) d
      _              -> d
      where
        w = weight e

    relaxGraph :: BFGraph -> Dist -> Dist
    relaxGraph g d = foldl relax d g

    update :: Eq a => a -> b -> [(a, b)] -> [(a, b)]
    update k v [] = [(k, v)]
    update k v ((k', v'):xs)
      | k == k'   = (k, v) : xs
      | otherwise = (k', v') : update k v xs

    hasNegativeCycle :: Dist -> BFGraph -> Bool
    hasNegativeCycle d = any (isRelaxable d)
      where
        isRelaxable :: Dist -> BFEdge -> Bool
        isRelaxable d e = case (du d e, dv d e) of
          (Fin u, Fin v) -> v > u + w
          (Fin u, Inf)   -> True
          _              -> False
          where
            w = weight e

filterConstraints :: Term -> UnivConstraints -> UnivConstraints
filterConstraints m = filter (filterConstraint uVars)
  where
    filterConstraint :: Set Int -> UnivConstraint -> Bool
    filterConstraint vs (ULeq u v) = filterUniv vs u && filterUniv vs v
    filterConstraint vs (ULt u v)  = filterUniv vs u && filterUniv vs v

    filterUniv :: Set Int -> Universe -> Bool
    filterUniv vs (UVar i) = i `Set.member` vs
    filterUniv vs (ULvl _) = True
    filterUniv vs _        = False

    uVars :: Set Int
    uVars = getUnivVarsInTerm m

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

type InsUniv a = State (Int, UnivSub) a

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
    go (Univ (UVar i))          = do
      (univID, sub) <- get
      put (max univID (i + 1), sub)
      return $ Univ $ UVar i
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
