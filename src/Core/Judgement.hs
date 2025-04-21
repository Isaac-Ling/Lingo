module Core.Judgement where

import Core.Data
import Core.Error
import Core.Evaluation

import Data.ByteString.Lazy.Char8 (ByteString, pack)

-- Judgemental equality of terms/types is alpha-beta equivalence
instance Eq Term where
  m == n = isAlphaEquiv (eval m) (eval n)

isAlphaEquiv :: Term -> Term -> Bool
isAlphaEquiv (Var x) (Var y)                = x == y
isAlphaEquiv (Lam (x, t) m) (Lam (y, t') n) = isAlphaEquiv t t' && isAlphaEquiv m (sub (Var x) y n)
isAlphaEquiv (Pi (x, t) m) (Pi (y, t') n)   = isAlphaEquiv t t' && isAlphaEquiv m (sub (Var x) y n)
isAlphaEquiv (App m n) (App m' n')          = isAlphaEquiv m n && isAlphaEquiv m' n'
isAlphaEquiv Star Star                      = True
isAlphaEquiv Zero Zero                      = True
isAlphaEquiv One One                        = True
isAlphaEquiv (Univ i) (Univ j)              = i == j
isAlphaEquiv _ _                            = False

inferType :: Context -> Term -> CanError Term
-- Universes
inferType g (Univ i)       = Result (Univ (i + 1))

-- Base types
inferType g Zero           = Result (Univ 0)
inferType g One            = Result (Univ 0)

-- Primitive constants
inferType g Star           = Result One

inferType g (Pi (x, t) m)  = case (inferType g t, inferType ((x, t) : g) m) of
  (Result (Univ i), Result (Univ j)) -> if i == j then Result (Univ i) else Error FailedToInferType
  (Result _, Error er)               -> Error er
  (Error er, _)                      -> Error er
  (_, _)                             -> Error FailedToInferType

inferType g (Var x)        = case lookup x g of
  Just t  -> Result t
  Nothing -> Error FailedToInferType

inferType g (Lam (x, t) m) = case (inferType g t, inferType ((x, t) : g) m) of
  (Result (Univ _), Result t') -> Result (Pi (x, t) t')
  (Error er, _)                -> Error er
  (_, Error er)                -> Error er

inferType g (App e e')     = case (inferType g e, inferType g e') of
  (Result (Pi (x, t) t'), Result t'') -> if t == t'' then Result (sub t'' x t') else Error FailedToInferType
  (Result _, Error er)                -> Error er
  (Error er, _)                       -> Error er
  (_, _)                              -> Error FailedToInferType

-- A is a type <=> A : Univ i, for some i
isType :: Context -> Term -> Bool
isType g a = case inferType g a of
  Result (Univ _) -> True
  _               -> False

ctx :: Context -> Bool
ctx []         = True
ctx ((_, t):g) = isType g t && ctx g
