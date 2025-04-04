module Core.TypeChecking where

import Core.Data
import Core.Error

type Context = [(Term, Type)]

typeInfer :: Context -> Term -> CanError Type
typeInfer g e = Error Success

typeCheck :: Context -> Term -> ErrorCode
typeCheck g (Anno e t) = 
  case typeInfer g e of
    Result t' -> if t == t' then Success else TypeMismatch
    Error er  -> er
typeCheck g e = Success
