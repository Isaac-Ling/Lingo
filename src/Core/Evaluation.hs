module Core.Evaluation where

import Core.Data

eval :: Term -> Term
eval (Var x)           = Var x
eval (Anno x y)        = eval x
eval (Lam x y)         = Lam x (eval y)
