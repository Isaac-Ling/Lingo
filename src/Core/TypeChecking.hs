module Core.TypeChecking where

import Core.Data
import Core.Error

import Data.ByteString.Lazy.Char8 (ByteString, pack)

type Context = [(ByteString, Type)]

typeCheck :: Term -> CanError Type
typeCheck e = typeCheckWithContext [] e
  where
    typeCheckWithContext :: Context -> Term -> CanError Type
    typeCheckWithContext g Star                  = Result One
    typeCheckWithContext g (Flag _)              = Result Bool
    typeCheckWithContext g (Anno e t)            = case typeCheckWithContext g e of
      Result t' -> if t == t' then Result t else Error TypeMismatch
      Error er  -> Error er
    typeCheckWithContext g (Var x)               = case lookup x g of
      Just t  -> Result t
      Nothing -> Error FailedToInferType
    typeCheckWithContext g (Lam (VarAnno x t) e) = case typeCheckWithContext ((x, t) : g) e of
      Result t' -> Result (Arr t t')
      Error er  -> Error er
    typeCheckWithContext g (App e e')            = case (typeCheckWithContext g e, typeCheckWithContext g e') of
      (Result (Arr t t'), Result t'' ) -> if t == t'' then Result t' else Error FailedToInferType
      (Result _, Error er)             -> Error er
      (Error er, _)                    -> Error er
