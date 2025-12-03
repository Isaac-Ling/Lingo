module Core.Elaboration where

import Core.Term
import Core.Error
import Parsing.Parser

import Control.Monad ((<=<))
import Data.List (sortOn, elemIndex, (!?))
import Data.ByteString.Lazy.Char8 (ByteString, pack)

-- TODO: Check logic of this function
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
    go bs (SVar x)              = case elemIndex (Just x) bs of
      Just i  -> Var (Bound i)
      Nothing -> Var (Free x)
    go bs (SLam (x, Nothing, ex) m) = Lam (x, Nothing, ex) (go (Just x : bs) m)
    go bs (SLam (x, Just t, ex) m)  = Lam (x, Just $ go bs t, ex) (go (Just x : bs) m)
    go bs (SPi (x, t, ex) m)        = Pi (x, go bs t, ex) (go (x : bs) m)
    go bs (SSigma (x, t) m)         = Sigma (x, go bs t) (go (x : bs) m)
    go bs (SApp m (n, ex))          = App (go bs m) (go bs n, ex)
    go bs (SPair m n)               = Pair (go bs m) (go bs n)
    go bs (SSum m n)                = Sum (go bs m) (go bs n)
    go bs (SIdFam t)                = IdFam $ go bs t
    go bs (SId t m n)               = Id (fmap (go bs) t) (go bs m) (go bs n)
    go bs (SInd t m c a)            = Ind (go bs t) (boundTermToCoreTerm bs m) (map (boundTermToCoreTerm bs) c) (go bs a)
    go bs (SUniv i)                 = Univ i
    go bs SBot                      = Bot
    go bs STop                      = Top
    go bs SNat                      = Nat
    go bs SZero                     = Zero
    go bs (SSucc m)                 = Succ $ go bs m
    go bs (SInl m)                  = Inl $ go bs m
    go bs (SInr m)                  = Inr $ go bs m
    go bs (SFunext p)               = Funext $ go bs p
    go bs (SUnivalence f)           = Univalence $ go bs f
    go bs (SRefl m)                 = Refl $ fmap (go bs) m
    go bs SStar                     = Star
    go bs (SParamTerm ps m)         = go bs $ paramsToBinders ps m

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

elaboratePatternMatchedDefs :: ByteString -> [SourceTerm] -> SourceTerm -> CanError SourceTerm
elaboratePatternMatchedDefs id [] _   = Error SyntaxError $ Just "Empty pattern matching cases"
elaboratePatternMatchedDefs id defs t = do
  -- Expand default paramaters into cases to get full pattern tree
  cases <- expandDefaultParams defs

  -- Elaborate each column starting from the leaves
  elaborateColumns id cases t
  where
    expandDefaultParams :: [SourceTerm] -> CanError [SourceTerm]
    expandDefaultParams defs = do
      n <- maxColumns defs 0

      expandDefaultParamsInColumns defs n

    expandDefaultParamsInColumns :: [SourceTerm] -> Int -> CanError [SourceTerm]
    expandDefaultParamsInColumns defs 0 = return defs
    expandDefaultParamsInColumns defs i = do
      patternMatched <- isColumnPatternMatched defs i
      let nextCol = i - 1

      if patternMatched
      then do
        expandedColumn <- traverse (`expandDefaultParamsInRow` i) defs
        expandDefaultParamsInColumns (concat expandedColumn) nextCol
      else expandDefaultParamsInColumns defs nextCol

    expandDefaultParamsInRow :: SourceTerm -> Int -> CanError [SourceTerm]
    expandDefaultParamsInRow p@(SParamTerm ps m) i = case ps !? i of
        Just (BinderParam (x, _, _)) -> do
          return p
        Just (Pattern _)             -> return [p]
        Nothing                      -> Error SyntaxError $ Just "Insufficient parameters"
    expandDefaultParamsInRow _ _                 = Error SyntaxError $ Just "Invalid pattern matching case"

    getPatternsFromType :: SourceTerm -> CanError [ConstructorPattern]
    getPatternsFromType STop         = return [CStar]
    getPatternsFromType SNat         = return [CZero, CSucc $ pack "!n"]
    getPatternsFromType (SSigma _ _) = return [CPair (pack "!a") (pack "!b")]
    getPatternsFromType (SSum _ _)   = return [CInl $ pack "!l", CInr $ pack "!r"]
    getPatternsFromType _                                   = Error SyntaxError $ Just "Not a pattern matched type"

    maxColumns :: [SourceTerm] -> Int -> CanError Int
    maxColumns [] i                   = return i
    maxColumns (SParamTerm ps _:ms) i = maxColumns ms $ max i $ length ps
    maxColumns _ _                    = Error SyntaxError $ Just "Invalid pattern matching case"

    elaborateColumns :: ByteString -> [SourceTerm] -> SourceTerm -> CanError SourceTerm
    elaborateColumns id defs t = do
      cases <- pushBinderParams defs

      -- Partition cases into patterns with the same parent parameters
      let patterns = partitionBy hasSameParentParameters cases

      leaves <- traverse (\x -> toEliminator id x t) patterns

      -- Recursively elaborate leaves until singular, non-pattern matched root remains
      case leaves of
        []  -> Error SyntaxError $ Just "Empty pattern matching cases"
        [d] -> if isPatternMatched d
          then do elaborateColumns id [d] t
          else return d
        ds  -> if not $ all isPatternMatched ds
          then Error SyntaxError $ Just "Empty pattern matching cases"
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

    pushBinderParams :: [SourceTerm] -> CanError [SourceTerm]
    pushBinderParams ps = do
      patternMatched <- isColumnPatternMatched ps 0

      if not patternMatched
      then do
        pushedBinders <- traverse pushParam ps
        pushBinderParams pushedBinders
      else return ps
      where
        pushParam :: SourceTerm -> CanError SourceTerm
        pushParam (SParamTerm (p:ps) m) = return $ SParamTerm ps $ paramsToBinders [p] m
        pushParam _                     = Error SyntaxError $ Just "Invalid pattern matching case"

    isColumnPatternMatched :: [SourceTerm] -> Int -> CanError Bool
    isColumnPatternMatched (SParamTerm ps _:ms) i = case ps !? i of
      Just p  -> do
        c <- isColumnPatternMatched ms i
        return $ isParameterPattern p && c
      Nothing -> return False
    isColumnPatternMatched [] _                   = return True
    isColumnPatternMatched _ _                    = Error SyntaxError $ Just "Misaligned patterns"

toEliminator :: ByteString -> [SourceTerm] -> SourceTerm -> CanError SourceTerm
toEliminator id [] _                               = Error SyntaxError $ Just "Empty pattern matching cases"
toEliminator id cases@((SParamTerm (p:ps) m):ms) t = do
  -- Get codomain of function to determine the motive
  codomain <- peelOffNBinders t $ length ps

  (indType, motive) <- case codomain of
    SPi (Just x, t, _) n  -> return (t, SBind x $ SNoBind n)
    SPi (Nothing, t, _) n -> return (t, SNoBind n)
    _                     -> Error TypeMismatch $ Just "Pattern matched function is not a Pi Type"

  patterns <- traverse getPattern cases

  -- TODO: Lambda abstract over all parameters to ensure different parameter names don't become free
  -- Match constructor patterns against exhaustive list
  ind <- case sortOn fst patterns of
    [(CStar, d)]                -> return $ SInd indType motive [SNoBind d] (SVar $ pack "!p")
    [(CPair a b, d)]            -> return $ SInd indType motive [SBind a $ SBind b $ SNoBind d] (SVar $ pack "!p")
    [(CInl a, d), (CInr b, d')] -> return $ SInd indType motive [SBind a $ SNoBind d, SBind b $ SNoBind d'] (SVar $ pack "!p")
    [(CZero, d), (CSucc n, d')] -> do
      let recursiveCallVar        = pack "!r"
      let recursiveCall           = SApp (applyParams ps $ SVar id) (SVar n, Exp)
      let abstractedRecursiveCall = substituteVarForApplication recursiveCallVar recursiveCall d'

      return $ SInd indType motive [SNoBind d, SBind n $ SBind recursiveCallVar $ SNoBind abstractedRecursiveCall] (SVar $ pack "!p")
    _                           -> Error SyntaxError $ Just "Invalid pattern matching constructors"

  -- Return eliminator term
  return $ SParamTerm (BinderParam (pack "!p", Just indType, Exp) : ps) ind
  where
    getPattern :: SourceTerm -> CanError (ConstructorPattern, SourceTerm)
    getPattern (SParamTerm (p:_) m) = do
      consPattern <- getConstructorPattern p
      return (consPattern, m)
    getPattern _                     = Error SyntaxError $ Just "Term is not a pattern"

    applyParams :: [Parameter] -> SourceTerm -> SourceTerm
    applyParams [] m                            = m
    applyParams ((BinderParam (x, _, ex)):ps) m = applyParams ps $ SApp m (SVar x, ex)
    applyParams ((Pattern pat):ps) m            = applyParams ps $ SApp m (pat, Exp)

    peelOffNBinders :: SourceTerm -> Int -> CanError SourceTerm
    peelOffNBinders m n
      | n <= 0    = return m
      | otherwise = go [] m n
      where
        go :: [SourcePiBinder] -> SourceTerm -> Int -> CanError SourceTerm
        go bs m 0                   = return m
        go bs (SPi (x, t, ex) m) n  = go bs m (n - 1)
        go bs m n                   = Error SyntaxError $ Just "Insufficient binders in type"

    substituteVarForApplication :: ByteString -> SourceTerm -> SourceTerm -> SourceTerm
    substituteVarForApplication y m (SApp t (n, ex))          = if SApp t (n, ex) == m
      then SVar y
      else SApp (substituteVarForApplication y m t) (substituteVarForApplication y m n, ex)
    substituteVarForApplication y m (SLam (x, Just t, ex) n)  = SLam (x, Just $ substituteVarForApplication y m t, ex) (substituteVarForApplication y m n)
    substituteVarForApplication y m (SLam (x, Nothing, ex) n) = SLam (x, Nothing, ex) (substituteVarForApplication y m n)
    substituteVarForApplication y m (SPi (x, t, ex) n)        = SPi (x, substituteVarForApplication y m t, ex) (substituteVarForApplication y m n)
    substituteVarForApplication y m (SSigma (x, t) n)         = SSigma (x, substituteVarForApplication y m t) (substituteVarForApplication y m n)
    substituteVarForApplication y m (SPair t n)               = SPair (substituteVarForApplication y m t) (substituteVarForApplication y m n)
    substituteVarForApplication y m (SIdFam t)                = SIdFam $ substituteVarForApplication y m t
    substituteVarForApplication y m (SId mt t n)              = SId (fmap (substituteVarForApplication y m) mt) (substituteVarForApplication y m t) (substituteVarForApplication y m n)
    substituteVarForApplication y m (SSum t n)                = SSum (substituteVarForApplication y m t) (substituteVarForApplication y m n)
    substituteVarForApplication y m (SInl n)                  = SInl $ substituteVarForApplication y m n
    substituteVarForApplication y m (SInr n)                  = SInr $ substituteVarForApplication y m n
    substituteVarForApplication y m (SRefl n)                 = SRefl $ fmap (substituteVarForApplication y m) n
    substituteVarForApplication y m (SSucc n)                 = SSucc $ substituteVarForApplication y m n
    substituteVarForApplication y m (SFunext p)               = SFunext $ substituteVarForApplication y m p
    substituteVarForApplication y m (SUnivalence a)           = SUnivalence $ substituteVarForApplication y m a
    substituteVarForApplication y m (SInd t m' c a)           = SInd (substituteVarForApplication y m t) (substituteVarForApplicationInBoundTerm y m m') (map (substituteVarForApplicationInBoundTerm y m) c) (substituteVarForApplication y m a)
      where
        substituteVarForApplicationInBoundTerm :: ByteString -> SourceTerm -> SourceBoundTerm -> SourceBoundTerm
        substituteVarForApplicationInBoundTerm y m (SNoBind n) = SNoBind (substituteVarForApplication y m n)
        substituteVarForApplicationInBoundTerm y m (SBind x n) = SBind x (substituteVarForApplicationInBoundTerm y m n)
    substituteVarForApplication y m n                        = n
toEliminator _ _ _                                = Error SyntaxError $ Just "Invalid pattern matching cases"

isParameterPattern :: Parameter -> Bool
isParameterPattern (Pattern _) = True
isParameterPattern _           = False

isPatternMatched :: SourceTerm -> Bool
isPatternMatched (SParamTerm ps _) = any isParameterPattern ps
isPatternMatched _                 = False
