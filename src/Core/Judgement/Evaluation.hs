module Core.Judgement.Evaluation where

import Core.Term
import Core.Error
import Core.Judgement.Utils

import Data.ByteString.Lazy.Char8 (ByteString)

eval :: Term -> Term
eval = id

-- Judgemental equality of terms/types is alpha-beta-eta equivalence
instance JudgementalEq Term where
  (===) m n env = eval (resolve env m) == eval (resolve env n)

instance JudgementalEq BoundTerm where
  (===) m n env = evalBoundTerm (resolveBoundTerm env m) == evalBoundTerm (resolveBoundTerm env n)
    where
      evalBoundTerm :: BoundTerm -> BoundTerm
      evalBoundTerm (NoBind m) = NoBind (eval m)
      evalBoundTerm (Bind m)   = evalBoundTerm m

      resolveBoundTerm :: Environment -> BoundTerm -> BoundTerm
      resolveBoundTerm env (NoBind m) = NoBind (resolve env m)
      resolveBoundTerm env (Bind m)   = resolveBoundTerm env m
