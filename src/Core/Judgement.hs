module Core.Judgement where

import Core.Data

isType :: Context -> Term -> Bool
isType g (Univ _) = True
isType g Zero     = True
isType g One      = True
isType g _        = False

ctx :: Context -> Bool
ctx []         = True
ctx ((_, t):g) = isType g t && ctx g
