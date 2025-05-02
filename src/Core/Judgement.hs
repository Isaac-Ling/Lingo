module Core.Judgement where

import Core.Data
import Core.Error
import Core.Evaluation

import Data.ByteString.Lazy.Char8 (ByteString, unpack)

-- Judgemental equality of terms/types is alpha-beta-eta equivalence
instance Eq Term where
  m == n = isAlphaEquiv (eval m) (eval n)

isAlphaEquiv :: Term -> Term -> Bool
isAlphaEquiv (Var x) (Var y)                    = x == y
isAlphaEquiv (Lam (x, t) m) (Lam (y, t') n)     = isAlphaEquiv t t' && isAlphaEquiv m (sub (Var x) y n)
isAlphaEquiv (Pi (x, t) m) (Pi (y, t') n)       = isAlphaEquiv t t' && isAlphaEquiv m (sub (Var x) y n)
isAlphaEquiv (Sigma (x, t) m) (Sigma (y, t') n) = isAlphaEquiv t t' && isAlphaEquiv m (sub (Var x) y n)
isAlphaEquiv (App m n) (App m' n')              = isAlphaEquiv m m' && isAlphaEquiv n n'
isAlphaEquiv (Pair m n) (Pair m' n')            = isAlphaEquiv m m' && isAlphaEquiv n n'
isAlphaEquiv Star Star                          = True
isAlphaEquiv Zero Zero                          = True
isAlphaEquiv One One                            = True
isAlphaEquiv (Univ i) (Univ j)                  = i == j
isAlphaEquiv _ _                                = False

typeCheck :: Context -> Term -> CanError Term
typeCheck g (Univ i)                      = Result (Univ (i + 1))
typeCheck g Zero                          = Result (Univ 0)
typeCheck g One                           = Result (Univ 0)
typeCheck g Star                          = Result One
typeCheck g (Pi (x, t) m)                 = case (typeCheck g t, typeCheck ((x, t) : g) m) of
  (Result (Univ i), Result (Univ j)) -> Result (Univ (max i j))
  (Result (Univ i), Result _)        -> Error TypeMismatch (Just (show m ++ " is not a term of a universe"))
  (Result _, Result _)               -> Error TypeMismatch (Just (show t ++ " is not a term of a universe"))
  (Error errc s, _)                  -> Error errc s
  (_, Error errc s)                  -> Error errc s
typeCheck g (Sigma (x, t) m) = case (typeCheck g t, typeCheck ((x, t) : g) m) of
  (Result (Univ i), Result (Univ j)) -> Result (Univ (max i j))
  (Result (Univ i), Result _)        -> Error TypeMismatch (Just (show m ++ " is not a term of a universe"))
  (Result _, Result _)               -> Error TypeMismatch (Just (show t ++ " is not a term of a universe"))
  (Error errc s, _)                  -> Error errc s
  (_, Error errc s)                  -> Error errc s
typeCheck g (Var x)                       = case lookup x g of
  Just t  -> Result t
  Nothing -> Error FailedToInferType (Just ("Unknown variable " ++ show x))
typeCheck g (Lam (x, t) m)                = case (typeCheck g t, typeCheck ((x, t) : g) m) of
  (Result (Univ _), Result t') -> Result (Pi (x, t) t')
  (Result _, Result _)         -> Error TypeMismatch (Just (show t ++ " is not a term of a universe"))
  (Error errc s, _)            -> Error errc s
  (_, Error errc s)            -> Error errc s
typeCheck g (App m n)                     = case (typeCheck g m, typeCheck g n) of
  (Result (Pi (x, t) t'), Result t'') -> if t == t'' then Result (sub n x t') else Error TypeMismatch (Just ("Type " ++ show (Pi (x, t) t') ++ " cannot be applied to type " ++ show t''))
  (Result _, Result _)                -> Error TypeMismatch (Just (show m ++ " is not a Pi type") )
  (Error errc s, _)                   -> Error errc s
  (_, Error errc s)                   -> Error errc s

-- TODO: This only supports non-dependent pairs, generalise it
typeCheck g (Pair m n)                    = case (typeCheck g m, typeCheck g n) of
  (Result t, Result t') -> Result (Sigma (getFreshVar n, t) t')
  (Error errc s, _)     -> Error errc s
  (_, Error errc s)     -> Error errc s

typeCheck g (Ind Zero (NoBind m) [] a)                    = typeCheck g (Ind Zero (Bind (getFreshVar m) (NoBind m)) [] a)
typeCheck g (Ind Zero (Bind x (NoBind m)) [] a)           = case (typeCheck ((x, Zero) : g) m, typeCheck g a) of
  (Result (Univ _), Result Zero) ->Result (sub a x m)
  -- TODO: Type check rest of zero induction

typeCheck g (Ind One (NoBind m) [NoBind c] a)             = typeCheck g (Ind One (Bind (getFreshVar m) (NoBind m)) [NoBind c] a)
typeCheck g (Ind One (Bind x (NoBind m)) [NoBind c] a)    = case (typeCheck ((x, One) : g) m, typeCheck g c, typeCheck g a) of
  (Result (Univ _), Result t, Result One) -> if t == sub Star x m then Result (sub a x m) else Error TypeMismatch (Just ("The term " ++ show c ++ " does not have the type of the motive " ++ show m))
  -- TODO: Type check rest of unit induction

-- A is a type <=> A : Univ i, for some i
isType :: Context -> Term -> Bool
isType g a = case typeCheck g a of
  Result (Univ _) -> True
  _               -> False

ctx :: Context -> Bool
ctx []         = True
ctx ((_, t):g) = isType g t && ctx g
