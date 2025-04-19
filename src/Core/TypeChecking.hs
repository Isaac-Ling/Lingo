module Core.TypeChecking where

import Core.Data
import Core.Error

import Data.ByteString.Lazy.Char8 (ByteString, pack)

typeCheck :: Term -> CanError Term
typeCheck = typeCheckWithContext []
  where
    typeCheckWithContext :: Context -> Term -> CanError Term
    typeCheckWithContext g (Univ i)       = Result (Univ (i + 1))
    typeCheckWithContext g Zero           = Result (Univ 0)
    typeCheckWithContext g One            = Result (Univ 0)
    typeCheckWithContext g Star           = Result One
    typeCheckWithContext g (Var x)        = case lookup x g of
      Just t  -> Result t
      Nothing -> Error FailedToInferType
    typeCheckWithContext g (Lam (x, t) m) = case typeCheckWithContext ((x, t) : g) m of
      Result t' -> Result (Pi (x, t) t')
      Error er  -> Error er
    typeCheckWithContext g (App e e')     = case (typeCheckWithContext g e, typeCheckWithContext g e') of
      (Result (Pi (x, t) t'), Result t'' ) -> if t == t'' then Result t' else Error FailedToInferType
      (Result _, Error er)                 -> Error er
      (Error er, _)                        -> Error er
