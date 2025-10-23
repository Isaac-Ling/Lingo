module Core.Elaboration where

import Core.Term
import Core.Error

import Control.Monad ((<=<))
import Data.ByteString.Lazy.Char8 (ByteString, pack)

-- TODO: Add implicit lambdas inside sub-terms ??
elaborateSource :: SourceTerm -> SourceTerm -> SourceTerm
elaborateSource (SPattern m n) (SPi (_, _, _) n')        = SPattern m $ elaborateSource n n'
elaborateSource (SLam (x, t, Imp) m) (SPi (_, _, Imp) n) = SLam (x, t, Imp) $ elaborateSource m n
elaborateSource m (SPi (Just x, t, Imp) n)               = SLam (x, Just t, Imp) $ elaborateSource m n
elaborateSource (SLam (x, t, Exp) m) (SPi (_, _, Exp) n) = SLam (x, t, Exp) $ elaborateSource m n
elaborateSource m _                                      = m

isPatternMatched :: SourceTerm -> Bool
isPatternMatched (SPattern _ _)     = True
isPatternMatched (SLam (_, _, _) m) = isPatternMatched m
isPatternMatched m                  = False

data ConstructorPattern
  = CStar
  | CPair ByteString ByteString
  | CInl ByteString
  | CInr ByteString
  deriving (Eq, Ord)

toEliminator :: [SourceTerm] -> SourceTerm -> CanError SourceTerm
toEliminator [] _     = Error SyntaxError $ Just "Empty pattern matching cases"
toEliminator ms t = do
  let splits            = map peelOffLambdas ms
  let firstBinderCount = length $ fst $ head splits 

  -- Check all patterns are at the same parameter number
  if all (isSplitValid firstBinderCount) splits
  then do
    -- Get codomain of function to determine the motive
    peelT <- peelOffNLambdas t firstBinderCount
    
    (indType, motive) <- case snd peelT of
      SPi (Just x, t, _) n  -> return (t, SBind x $ SNoBind n)
      SPi (Nothing, t, _) n -> return (t, SNoBind n)
      _                     -> Error TypeMismatch $ Just "Pattern matched function is not a Pi Type"

    patterns <- traverse (splitPattern . snd) splits

    -- Match constructor patterns against exhaustive list
    case patterns of
      [(CStar, p)]     -> return $ SLam (pack "!p", Nothing, Exp) $ SInd indType motive [SNoBind p] (SVar $ pack "!p")
      [(CPair a b, p)] -> return $ SLam (pack "!p", Nothing, Exp) $ SInd indType motive [SBind a $ SBind b $ SNoBind p] (SVar $ pack "!p")
      _       -> Error SyntaxError $ Just "Invalid pattern matching constructors"
  else
    Error SyntaxError $ Just "Pattern matching parameter mismatch"

  where
    headIsPattern :: SourceTerm -> Bool
    headIsPattern (SPattern _ _) = True
    headIsPattern _              = False

    splitPattern :: SourceTerm -> CanError (ConstructorPattern, SourceTerm)
    splitPattern (SPattern m n) = do
      cons <- getConstructorPattern m
      return (cons, n)
    splitPattern _              = Error SyntaxError $ Just "Term is not a pattern"

    getConstructorPattern :: SourceTerm -> CanError ConstructorPattern
    getConstructorPattern SStar                     = return CStar
    getConstructorPattern (SPair (SVar a) (SVar b)) = return $ CPair a b
    getConstructorPattern (SInl (SVar a))           = return $ CInl a
    getConstructorPattern (SInr (SVar a))           = return $ CInr a
    getConstructorPattern _                         = Error SyntaxError $ Just "Invalid pattern matching constructor"

    peelOffLambdas :: SourceTerm -> ([SourceLambdaBinder], SourceTerm)
    peelOffLambdas m = go [] m
      where
        go :: [SourceLambdaBinder] -> SourceTerm -> ([SourceLambdaBinder], SourceTerm)
        go bs (SLam (x, t, ex) m) = go ((x, t, ex) : bs) m
        go bs m                   = (bs, m)

    peelOffNLambdas :: SourceTerm -> Int -> CanError ([SourceLambdaBinder], SourceTerm)
    peelOffNLambdas m n
      | n <= 0    = return ([], m)
      | otherwise = go [] m n
      where
        go :: [SourceLambdaBinder] -> SourceTerm -> Int -> CanError ([SourceLambdaBinder], SourceTerm)
        go bs m 0                   = return (bs, m)
        go bs (SLam (x, t, ex) m) n = go ((x, t, ex) : bs) m (n - 1)
        go bs m n                   = Error SyntaxError $ Just "Insufficient binders in type"

    isSplitValid :: Int -> ([SourceLambdaBinder], SourceTerm) -> Bool
    isSplitValid n (bs, m) = headIsPattern m && length bs == n
