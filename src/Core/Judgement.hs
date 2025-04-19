module Core.Judgement where

import Core.Data

-- A is a type <=> A : Ui for some i
isType :: Context -> Term -> Bool
isType g (Var x)   = case lookup x g of
  Just t  -> isType g t
  Nothing -> False
isType g (Lam _ _) = False
isType g (App _ _) = False  -- TODO: Finish this
isType g _         = True

ctx :: Context -> Bool
ctx []         = True
ctx ((_, t):g) = isType g t && ctx g
