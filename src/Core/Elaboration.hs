{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}
module Core.Elaboration where

import Core.Term
import Core.Error
import Parsing.Parser
import Core.Judgement.Evaluation

import Control.Monad ((<=<), unless, replicateM)
import Data.List (sortOn, elemIndex, (!?))
import Data.ByteString.Lazy.Char8 (ByteString, pack)
import Control.Monad.State.Lazy

addImplicitParameters :: SourceTerm -> SourceTerm -> SourceTerm
addImplicitParameters (SLam (x, t, Imp) m) (SPi (_, _, Imp) n) = addImplicitParameter (BinderParam (x, t, Imp)) $ addImplicitParameters m n
addImplicitParameters m (SPi (Just x, t, Imp) n)               = addImplicitParameter (BinderParam (x, Just t, Imp)) $ addImplicitParameters m n
addImplicitParameters (SLam (x, t, Exp) m) (SPi (_, _, Exp) n) = addImplicitParameter (BinderParam (x, t, Exp)) $ addImplicitParameters m n
addImplicitParameters m _                                      = m

addImplicitParameter :: Parameter -> SourceTerm  -> SourceTerm
addImplicitParameter p (SParamTerm ps m) = SParamTerm (ps ++ [p]) m
addImplicitParameter p m                 = SParamTerm [p] m

paramsToBinders :: [Parameter] -> SourceTerm -> SourceTerm
paramsToBinders [] m                   = m
paramsToBinders ((BinderParam b):bs) m = paramsToBinders bs $ SLam b m
paramsToBinders (_:bs) m               = paramsToBinders bs m

toCoreTerm :: SourceTerm -> Term
toCoreTerm = go []
  where
    go :: Binders -> SourceTerm -> Term
    go bs (SVar x)                         = case elemIndex (Just x) bs of
      Just i  -> Var (Bound i)
      Nothing -> Var (Free x)
    go bs (SLam (x, Nothing, ex) m)        = Lam (x, Nothing, ex) (go (Just x : bs) m)
    go bs (SLam (x, Just t, ex) m)         = Lam (x, Just $ go bs t, ex) (go (Just x : bs) m)
    go bs (SPi (x, t, ex) m)               = Pi (x, go bs t, ex) (go (x : bs) m)
    go bs (SSigma (x, t) m)                = Sigma (x, go bs t) (go (x : bs) m)
    go bs (SApp m (n, ex))                 = App (go bs m) (go bs n, ex)
    go bs (SPair m n)                      = Pair (go bs m) (go bs n)
    go bs (SSum m n)                       = Sum (go bs m) (go bs n)
    go bs (SIdFam t)                       = IdFam $ go bs t
    go bs (SId t m n)                      = Id (fmap (go bs) t) (go bs m) (go bs n)
    go bs (SInd t m c a)                   = Ind (go bs t) (boundTermToCoreTerm bs m) (map (boundTermToCoreTerm bs) c) (go bs a)
    go bs (SUniv i)                        = Univ i
    go bs SBot                             = Bot
    go bs STop                             = Top
    go bs SNat                             = Nat
    go bs SZero                            = Zero
    go bs (SSucc m)                        = Succ $ go bs m
    go bs (SInl m)                         = Inl $ go bs m
    go bs (SInr m)                         = Inr $ go bs m
    go bs (SFunext p)                      = Funext $ go bs p
    go bs (SUnivalence f)                  = Univalence $ go bs f
    go bs (SRefl m)                        = Refl $ fmap (go bs) m
    go bs SStar                            = Star
    go bs (SParamTerm ps m)                = go bs $ paramsToBinders ps m
    go bs (SubstitutionTerm [] m)          = go bs m
    go bs (SubstitutionTerm ((x, y):ss) m) = beta $ go bs $ SubstitutionTerm ss $ SApp (SLam (y, Nothing, Exp) m) (x, Exp)

    boundTermToCoreTerm :: Binders -> SourceBoundTerm -> BoundTerm
    boundTermToCoreTerm bs (SNoBind m) = NoBind $ go bs m
    boundTermToCoreTerm bs (SBind x m) = Bind (Just x) $ boundTermToCoreTerm (Just x : bs) m

-- TODO: Support nested constructor patterns
data ConstructorPattern
  = CStar
  | CPair ByteString ByteString
  | CInl ByteString
  | CInr ByteString
  | CZero
  | CSucc ByteString
  deriving (Show, Eq, Ord)

getConstructorPattern :: Parameter -> CanError ConstructorPattern
getConstructorPattern (Pattern SStar)                     = return CStar
getConstructorPattern (Pattern (SPair (SVar a) (SVar b))) = return $ CPair a b
getConstructorPattern (Pattern (SInl (SVar a)))           = return $ CInl a
getConstructorPattern (Pattern (SInr (SVar a)))           = return $ CInr a
getConstructorPattern (Pattern SZero)                     = return CZero
getConstructorPattern (Pattern (SSucc (SVar n)))          = return $ CSucc n
getConstructorPattern _                                   = Error SyntaxError $ Just "Invalid pattern matching constructor"

data ElaborateState = ElaborateState
  { freshVarID :: Int
  }
 
type Elaborate a = StateT ElaborateState CanError a

getFreshVar :: String -> Elaborate ByteString
getFreshVar x = do
  st <- get
  let i = freshVarID st
  put $ st { freshVarID = i + 1 }
  return $ pack ("!" ++ x ++ show i)

patternSyntaxError :: Maybe String -> Elaborate a
patternSyntaxError ms = lift $ Error SyntaxError ms

elaboratePatternMatchedDefs :: ByteString -> [SourceTerm] -> SourceTerm -> CanError SourceTerm
elaboratePatternMatchedDefs id defs t = evalStateT (goElaboratePatternMatchedDefs id defs t) st
  where
    st = ElaborateState { freshVarID=0 }

goElaboratePatternMatchedDefs :: ByteString -> [SourceTerm] -> SourceTerm -> Elaborate SourceTerm
goElaboratePatternMatchedDefs _ [] _    = patternSyntaxError $ Just "Empty pattern matching cases"
goElaboratePatternMatchedDefs id defs t = do
  -- Expand default paramaters into cases to get full case tree
  cases <- expandDefaultParams defs

  -- Elaborate each column starting from the leaves
  elaborateColumns id cases t
  where
    expandDefaultParams :: [SourceTerm] -> Elaborate [SourceTerm]
    expandDefaultParams defs = do
      n <- maxColumnIndex defs 0

      expandDefaultParamsInColumns defs n

    expandDefaultParamsInColumns :: [SourceTerm] -> Int -> Elaborate [SourceTerm]
    expandDefaultParamsInColumns defs (-1) = return defs
    expandDefaultParamsInColumns defs i    = do
      patternMatched <- isColumnPatternMatched defs i
      let nextCol = i - 1

      if patternMatched
      then do
        patterns       <- getPatternsFromColumn defs i
        expandedColumn <- traverse (\x -> expandDefaultParamsInRow x i patterns) defs

        expandDefaultParamsInColumns (concat expandedColumn) nextCol
      else expandDefaultParamsInColumns defs nextCol

    expandDefaultParamsInRow :: SourceTerm -> Int -> [SourceTerm] -> Elaborate [SourceTerm]
    expandDefaultParamsInRow p@(SParamTerm ps m) i cs = case ps !? i of
      -- Abstract over the default parameter with the expanded patterns
      Just (BinderParam (x, _, _)) -> return $ map (constructorToAbstractedSourceTerm ps i m x) cs
      Just (Pattern _)             -> return [p]
      Nothing                      -> patternSyntaxError $ Just "Insufficient parameters"
    expandDefaultParamsInRow _ _ _                    = patternSyntaxError $ Just "Invalid pattern matching case"

    constructorToAbstractedSourceTerm :: [Parameter] -> Int -> SourceTerm -> ByteString -> SourceTerm -> SourceTerm
    --constructorToAbstractedSourceTerm ps i m x c = SParamTerm (replaceAt ps i (Pattern c)) $ SApp (SLam (x, Nothing, Exp) m) (c, Exp)
    constructorToAbstractedSourceTerm ps i m x c = SParamTerm (replaceAt ps i (Pattern c)) $ SubstitutionTerm [(c, x)] m

    replaceAt :: [a] -> Int -> a -> [a]    
    replaceAt xs i x = take i xs ++ [x] ++ drop (i + 1) xs

    getPatternsFromColumn :: [SourceTerm] -> Int -> Elaborate [SourceTerm]
    getPatternsFromColumn [] _                       = patternSyntaxError $ Just "No patterns in column"
    getPatternsFromColumn ((SParamTerm ps m):defs) i = case ps !? i of
      Just (BinderParam _) -> getPatternsFromColumn defs i
      Just p@(Pattern _)   -> do
        p <- lift $ getConstructorPattern p
        getPatternsFromConstructor p
      Nothing              -> patternSyntaxError $ Just "Insufficient parameters"

    getPatternsFromConstructor :: ConstructorPattern -> Elaborate [SourceTerm]
    getPatternsFromConstructor CStar       = return [SStar]
    getPatternsFromConstructor CZero       = do
      id <- getFreshVar "n"
      return [SZero, SSucc $ SVar id]
    getPatternsFromConstructor (CSucc _)   = do
      id <- getFreshVar "n"
      return [SZero, SSucc $ SVar id]
    getPatternsFromConstructor (CPair _ _) = do
      id1 <- getFreshVar "a"
      id2 <- getFreshVar "b"
      return [SPair (SVar id1) (SVar id2)]
    getPatternsFromConstructor (CInl _)    = do
      id1 <- getFreshVar "a"
      id2 <- getFreshVar "b"
      return [SInl $ SVar id1, SInr $ SVar id2]
    getPatternsFromConstructor (CInr _)    = do
      id1 <- getFreshVar "l"
      id2 <- getFreshVar "r"
      return[SInl $ SVar id1, SInr $ SVar id2]

    maxColumnIndex :: [SourceTerm] -> Int -> Elaborate Int
    maxColumnIndex [] i                   = return i
    maxColumnIndex (SParamTerm ps _:ms) i = maxColumnIndex ms $ max i $ length ps - 1
    maxColumnIndex _ _                    = patternSyntaxError $ Just "Invalid pattern matching case"

    elaborateColumns :: ByteString -> [SourceTerm] -> SourceTerm -> Elaborate SourceTerm
    elaborateColumns id defs t = do
      cases <- pushBinderParams defs

      -- Partition cases into patterns with the same parent parameters
      let rawPatterns = partitionBy hasSameParentParameters cases

      -- Normalise parent identifiers
      patterns <- traverse normaliseParentBinders rawPatterns

      -- Collapse patterns into eliminators
      leaves <- traverse (\x -> toEliminator id x t) patterns

      -- Recursively elaborate leaves until singular, non-pattern matched root remains
      case leaves of
        []  -> patternSyntaxError $ Just "Empty pattern matching cases"
        [d] -> if isPatternMatched d
          then do elaborateColumns id [d] t
          else return d
        ds  -> if not $ all isPatternMatched ds
          then patternSyntaxError $ Just "Failed to collapse case tree into single eliminator"
          else do elaborateColumns id ds t

    partitionBy :: (a -> a -> Bool) -> [a] -> [[a]]
    partitionBy eq = go []
      where
        go bs []     = bs
        go bs (x:xs) = go (insert x bs) xs

        insert x [] = [[x]]
        insert x (b:bs)
          | all (eq x) b = (x:b) : bs
          | otherwise    = b : insert x bs

    normaliseParentBinders :: [SourceTerm] -> Elaborate [SourceTerm]
    normaliseParentBinders []  = return []
    normaliseParentBinders [a] = return [a]
    normaliseParentBinders ms  = do
      n <- maxColumnIndex ms 0
      goNormaliseParentBinders ms n
      where
        goNormaliseParentBinders :: [SourceTerm] -> Int -> Elaborate [SourceTerm]
        goNormaliseParentBinders [] _ = patternSyntaxError $ Just "Insufficient parameters"
        goNormaliseParentBinders ms 0 = return ms
        goNormaliseParentBinders ms i = do
          xs <- getBindersInColumn ms i []

          -- Abstract RHSs over a single fresh binder if they are not the same across cases
          ms' <- if not $ allSame xs
            then do
              let allSameLengths = allSame $ map length xs

              case (xs, allSameLengths) of
                (x:_, True) -> do
                  normalisedBinders <- replicateM (length x) (getFreshVar "a")
                  traverse (\m -> useFreshBinders m i normalisedBinders) ms 
                _             -> patternSyntaxError $ Just "Mismatched constructors"
            else do
              return ms

          goNormaliseParentBinders ms' (i - 1)

        allSame :: Eq a => [a] -> Bool
        allSame []     = True
        allSame (x:xs) = all (== x) xs

        useFreshBinders :: SourceTerm -> Int -> [ByteString] -> Elaborate SourceTerm
        useFreshBinders (SParamTerm ps m) i xs = do
          (ys, c) <- case ps !? i of
            Just (BinderParam (y, _, _)) -> case xs of
              [x] -> return ([y], SVar x)
              _   -> patternSyntaxError $ Just "Unable to remap to fresh binders"
            Just p@(Pattern _)           -> do
              c <- lift $ getConstructorPattern p
              case (c, xs) of
                (CPair a b, [x1, x2]) -> return ([a, b], SPair (SVar x1) (SVar x2))
                (CInl l, [x])         -> return ([l], SInl $ SVar x)
                (CInr r, [x])         -> return ([r], SInr $ SVar x)
                (CSucc n, [x])        -> return ([n], SSucc $ SVar x)
                _           -> patternSyntaxError $ Just "Unable to remap to fresh binders"
            Nothing                      -> patternSyntaxError $ Just "Insufficient parameters"

          let ps' = replaceAt ps i (Pattern c)

          return $ SParamTerm ps' $ SubstitutionTerm (zip (map SVar xs) ys) m
        useFreshBinders _ _ _                  = patternSyntaxError $ Just "Term is not a parameterised term"

        getBindersInColumn :: [SourceTerm] -> Int -> [[ByteString]] -> Elaborate [[ByteString]]
        getBindersInColumn [] _ xs                       = return xs
        getBindersInColumn ((SParamTerm ps m):defs) i xs = case ps !? i of
          Just (BinderParam (x, _, _)) -> getBindersInColumn defs i ([x]:xs)
          Just p@(Pattern _)           -> do
            p <- lift $ getConstructorPattern p

            let x = case p of
                      (CPair a b) -> [a, b]
                      (CInl l)    -> [l]
                      (CInr r)    -> [r]
                      (CSucc n)   -> [n]
                      _           -> []

            getBindersInColumn defs i (x:xs)
          Nothing                      -> patternSyntaxError $ Just "Insufficient parameters"

    hasSameParentParameters :: SourceTerm -> SourceTerm -> Bool
    hasSameParentParameters (SParamTerm [] _) (SParamTerm _ _)           = False
    hasSameParentParameters (SParamTerm _ _) (SParamTerm [] _)           = False
    hasSameParentParameters (SParamTerm (_:ps) _) (SParamTerm (_:ps') _) = (length ps == length ps') && and (zipWith hasSameParameterStructure ps ps')
    hasSameParentParameters _ _                                          = False

    hasSameParameterStructure :: Parameter -> Parameter -> Bool
    hasSameParameterStructure (BinderParam _) (BinderParam _) = True
    hasSameParameterStructure p p'                            = case (getConstructorPattern p, getConstructorPattern p') of
      (Result CStar, Result CStar)             -> True
      (Result (CPair _ _), Result (CPair _ _)) -> True
      (Result (CInl _), Result (CInl _))       -> True
      (Result (CInr _), Result (CInr _))       -> True
      (Result CZero, Result CZero)             -> True
      (Result (CSucc _), Result (CSucc _))     -> True
      (_, _)                                   -> False

    pushBinderParams :: [SourceTerm] -> Elaborate [SourceTerm]
    pushBinderParams ps = do
      patternMatched <- isColumnPatternMatched ps 0

      if not patternMatched
      then do
        pushedBinders <- traverse pushParam ps
        pushBinderParams pushedBinders
      else return ps
      where
        pushParam :: SourceTerm -> Elaborate SourceTerm
        pushParam (SParamTerm (p:ps) m) = return $ SParamTerm ps $ paramsToBinders [p] m
        pushParam _                     = patternSyntaxError $ Just "Invalid pattern matching case"

    isColumnPatternMatched :: [SourceTerm] -> Int -> Elaborate Bool
    isColumnPatternMatched (SParamTerm ps _:ms) i = case ps !? i of
      Just p  -> do
        c <- isColumnPatternMatched ms i
        return $ isParameterPattern p || c
      Nothing -> return False
    isColumnPatternMatched [] _                   = return False
    isColumnPatternMatched _ _                    = patternSyntaxError $ Just "Misaligned patterns"

toEliminator :: ByteString -> [SourceTerm] -> SourceTerm -> Elaborate SourceTerm
toEliminator id [] _                               = patternSyntaxError $ Just "Empty pattern matching cases"
toEliminator id cases@((SParamTerm (p:ps) m):ms) t = do
  -- Get codomain of function to determine the motive
  codomain <- subParamsInType t $ reverse ps

  (indType, motive) <- case codomain of
    SPi (Just x, t, _) n  -> return (t, SBind x $ SNoBind n)
    SPi (Nothing, t, _) n -> return (t, SNoBind n)
    _                     -> patternSyntaxError $ Just "Pattern matched function is not a Pi Type"

  patterns <- traverse getPattern cases

  -- Match constructor patterns against exhaustive list
  ind <- case sortOn fst patterns of
    [(CStar, d)]                -> return $ SInd indType motive [SNoBind d] (SVar $ pack "!p")
    [(CPair a b, d)]            -> return $ SInd indType motive [SBind a $ SBind b $ SNoBind d] (SVar $ pack "!p")
    [(CInl a, d), (CInr b, d')] -> return $ SInd indType motive [SBind a $ SNoBind d, SBind b $ SNoBind d'] (SVar $ pack "!p")
    [(CZero, d), (CSucc n, d')] -> do
      recursiveCallVar <- getFreshVar "r"
      let recursiveCall           = SApp (applyParams ps $ SVar id) (SVar n, Exp)
      let abstractedRecursiveCall = substituteVarForRecursiveCall [] [] recursiveCallVar recursiveCall d'

      return $ SInd indType motive [SNoBind d, SBind n $ SBind recursiveCallVar $ SNoBind abstractedRecursiveCall] (SVar $ pack "!p")
    _                           -> patternSyntaxError $ Just "Invalid pattern matching constructors"

  -- Return eliminator term
  return $ SParamTerm (BinderParam (pack "!p", Just indType, Exp) : ps) ind
  where
    getPattern :: SourceTerm -> Elaborate (ConstructorPattern, SourceTerm)
    getPattern (SParamTerm (p:_) m) = do
      consPattern <- lift $ getConstructorPattern p
      return (consPattern, m)
    getPattern _                     = patternSyntaxError $ Just "Term is not a pattern"

    applyParams :: [Parameter] -> SourceTerm -> SourceTerm
    applyParams [] m                            = m
    applyParams ((BinderParam (x, _, ex)):ps) m = applyParams ps $ SApp m (SVar x, ex)
    applyParams ((Pattern pat):ps) m            = applyParams ps $ SApp m (pat, Exp)

    subParamsInType :: SourceTerm -> [Parameter] -> Elaborate SourceTerm
    subParamsInType m []                           = return m
    subParamsInType (SPi (Nothing, _, _) m) (_:ps) = subParamsInType m ps
    subParamsInType (SPi (Just x, _, _) m) (p:ps)  = do
      t <- parameterToTerm p
      subParamsInType (subParamInType t x m) ps
      where
        parameterToTerm :: Parameter -> Elaborate SourceTerm
        parameterToTerm (Pattern m)             = return m
        parameterToTerm (BinderParam (x, _, _)) = return $ SVar x

        -- TODO: Avoid variable capture, e.g. subbing succ(n) in could capture n
        subParamInType :: SourceTerm -> ByteString -> SourceTerm -> SourceTerm
        subParamInType m x (SVar y)
          | x == y    = m
          | otherwise = SVar y
        subParamInType m x (SLam (y, Just t, ex) n)  = SLam (y, Just $ subParamInType m x t, ex) (subParamInType m x n)
        subParamInType m x (SLam (y, Nothing, ex) n) = SLam (y, Nothing, ex) (subParamInType m x n)
        subParamInType m x (SPi (y, t, ex) n)        = SPi (y, subParamInType m x t, ex) (subParamInType m x n)
        subParamInType m x (SSigma (y, t) n)         = SSigma (y, subParamInType m x t) (subParamInType m x n)
        subParamInType m x (SPair t n)               = SPair (subParamInType m x t) (subParamInType m x n)
        subParamInType m x (SIdFam t)                = SIdFam $ subParamInType m x t
        subParamInType m x (SId mt t n)              = SId (fmap (subParamInType m x) mt) (subParamInType m x t) (subParamInType m x n)
        subParamInType m x (SSum t n)                = SSum (subParamInType m x t) (subParamInType m x n)
        subParamInType m x (SApp t (n, ex))          = SApp (subParamInType m x t) (subParamInType m x n, ex)
        subParamInType m x (SInl n)                  = SInl $ subParamInType m x n
        subParamInType m x (SInr n)                  = SInr $ subParamInType m x n
        subParamInType m x (SRefl n)                 = SRefl $ fmap (subParamInType m x) n
        subParamInType m x (SSucc n)                 = SSucc $ subParamInType m x n
        subParamInType m x (SFunext p)               = SFunext $ subParamInType m x p
        subParamInType m x (SUnivalence a)           = SUnivalence $ subParamInType m x a
        subParamInType m x (SInd t m' c a)           = SInd (subParamInType m x t) (subParamInBoundType m x m') (map (subParamInBoundType m x) c) (subParamInType m x a)
          where
            subParamInBoundType :: SourceTerm -> ByteString -> SourceBoundTerm -> SourceBoundTerm
            subParamInBoundType m x (SNoBind n) = SNoBind (subParamInType m x n)
            subParamInBoundType m x (SBind y n) = SBind y (subParamInBoundType m x n)
        subParamInType m x n                         = n
    subParamsInType _ _                            = patternSyntaxError $ Just "Insufficient binders in type"

    substituteVarForRecursiveCall :: [(SourceTerm, ByteString)] -> [ByteString] -> ByteString -> SourceTerm -> SourceTerm -> SourceTerm
    substituteVarForRecursiveCall subs bs y m a@(SApp t (n, ex))        = if isApplicationRecursiveCall subs bs a m
      then SVar y
      else SApp (substituteVarForRecursiveCall subs bs y m t) (substituteVarForRecursiveCall subs bs y m n, ex)
      where
        -- Checks if an application is the same as a recursive call application, taking possible parameter substitutions and binders into account
        isApplicationRecursiveCall :: [(SourceTerm, ByteString)] -> [ByteString] -> SourceTerm -> SourceTerm -> Bool
        isApplicationRecursiveCall subs bs (SApp a (b, ex)) (SApp c (d, ex')) = ex == ex' && isApplicationRecursiveCall subs bs a c && isApplicationRecursiveCall subs bs b d
        isApplicationRecursiveCall subs bs (SVar x) (SVar y)                  = (x == y || (SVar y, x) `elem` subs) && x `notElem` bs
        isApplicationRecursiveCall subs bs STop STop                          = True
        isApplicationRecursiveCall subs bs SZero SZero                        = True
        isApplicationRecursiveCall subs bs (SSucc a) (SSucc b)                = isApplicationRecursiveCall subs bs a b
        isApplicationRecursiveCall subs bs (SInl a) (SInl b)                  = isApplicationRecursiveCall subs bs a b
        isApplicationRecursiveCall subs bs (SInr a) (SInr b)                  = isApplicationRecursiveCall subs bs a b
        isApplicationRecursiveCall subs bs (SPair a b) (SPair a' b')          = isApplicationRecursiveCall subs bs a a' && isApplicationRecursiveCall subs bs b  b'
        isApplicationRecursiveCall subs bs _ _                                = False
    substituteVarForRecursiveCall subs bs y m (SLam (x, Just t, ex) n)  = SLam (x, Just $ substituteVarForRecursiveCall subs bs y m t, ex) (substituteVarForRecursiveCall subs (x : bs) y m n)
    substituteVarForRecursiveCall subs bs y m (SLam (x, Nothing, ex) n) = SLam (x, Nothing, ex) (substituteVarForRecursiveCall subs (x : bs) y m n)
    substituteVarForRecursiveCall subs bs y m (SPi (x, t, ex) n)        = SPi (x, substituteVarForRecursiveCall subs bs y m t, ex) (substituteVarForRecursiveCall subs (maybe bs (:bs) x) y m n)
    substituteVarForRecursiveCall subs bs y m (SSigma (x, t) n)         = SSigma (x, substituteVarForRecursiveCall subs bs y m t) (substituteVarForRecursiveCall subs (maybe bs (:bs) x) y m n)
    substituteVarForRecursiveCall subs bs y m (SPair t n)               = SPair (substituteVarForRecursiveCall subs bs y m t) (substituteVarForRecursiveCall subs bs y m n)
    substituteVarForRecursiveCall subs bs y m (SIdFam t)                = SIdFam $ substituteVarForRecursiveCall subs bs y m t
    substituteVarForRecursiveCall subs bs y m (SId mt t n)              = SId (fmap (substituteVarForRecursiveCall subs bs y m) mt) (substituteVarForRecursiveCall subs bs y m t) (substituteVarForRecursiveCall subs bs y m n)
    substituteVarForRecursiveCall subs bs y m (SSum t n)                = SSum (substituteVarForRecursiveCall subs bs y m t) (substituteVarForRecursiveCall subs bs y m n)
    substituteVarForRecursiveCall subs bs y m (SInl n)                  = SInl $ substituteVarForRecursiveCall subs bs y m n
    substituteVarForRecursiveCall subs bs y m (SInr n)                  = SInr $ substituteVarForRecursiveCall subs bs y m n
    substituteVarForRecursiveCall subs bs y m (SRefl n)                 = SRefl $ fmap (substituteVarForRecursiveCall subs bs y m) n
    substituteVarForRecursiveCall subs bs y m (SSucc n)                 = SSucc $ substituteVarForRecursiveCall subs bs y m n
    substituteVarForRecursiveCall subs bs y m (SFunext p)               = SFunext $ substituteVarForRecursiveCall subs bs y m p
    substituteVarForRecursiveCall subs bs y m (SUnivalence a)           = SUnivalence $ substituteVarForRecursiveCall subs bs y m a
    substituteVarForRecursiveCall subs bs y m (SubstitutionTerm ss n)   = SubstitutionTerm ss $ substituteVarForRecursiveCall (ss ++ subs) bs y m n
    substituteVarForRecursiveCall subs bs y m (SInd t m' c a)           = SInd (substituteVarForRecursiveCall subs bs y m t) (substituteVarForRecursiveCallInBoundTerm subs bs y m m') (map (substituteVarForRecursiveCallInBoundTerm subs bs y m) c) (substituteVarForRecursiveCall subs bs y m a)
      where
        substituteVarForRecursiveCallInBoundTerm :: [(SourceTerm, ByteString)] -> [ByteString] -> ByteString -> SourceTerm -> SourceBoundTerm -> SourceBoundTerm
        substituteVarForRecursiveCallInBoundTerm subs bs y m (SNoBind n) = SNoBind (substituteVarForRecursiveCall subs bs y m n)
        substituteVarForRecursiveCallInBoundTerm subs bs y m (SBind x n) = SBind x (substituteVarForRecursiveCallInBoundTerm subs (x : bs) y m n)
    substituteVarForRecursiveCall subs bs y m n                        = n
toEliminator _ _ _                                = patternSyntaxError $ Just "Invalid pattern matching cases"

isParameterPattern :: Parameter -> Bool
isParameterPattern (Pattern _) = True
isParameterPattern _           = False

isPatternMatched :: SourceTerm -> Bool
isPatternMatched (SParamTerm ps _) = any isParameterPattern ps
isPatternMatched _                 = False
