module Core.TypeChecking where

import Core.Data
import Core.Error

import Data.ByteString.Lazy.Char8 (ByteString)

type Context = [(ByteString, Type)]

typeInfer :: Context -> Term -> CanError Type
typeInfer g (Var x)    = case mt of
  Just t  -> Result t
  Nothing -> Error FailedToInferType
  where
    mt = lookup x g
typeInfer _ (Anno _ _) = Error FailedToInferType
typeInfer g (Lam x e)  = typeInfer (g) e

typeCheck :: Term -> ErrorCode
typeCheck e = typeCheckWithContext [] e
  where
    typeCheckWithContext :: Context -> Term -> ErrorCode
    typeCheckWithContext g (Anno e t) = 
      case typeInfer g e of
        Result t' -> if t == t' then Success else TypeMismatch
        Error er  -> er
    typeCheckWithContext g e = Success
