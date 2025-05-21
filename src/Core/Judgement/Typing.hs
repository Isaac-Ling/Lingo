module Core.Judgement.Typing where

import Core.Term
import Core.Error
import Core.Judgement.Utils

import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString)

inferType :: Context -> Term -> CanError Term
inferType ctx m = runReaderT (runInferType m) ([], ctx)
  where
    runInferType :: Term -> TypeCheck Term
    runInferType Star = return One
    runInferType Zero = return $ Univ 0
    runInferType One  = return $ Univ 0
    runInferType m    = return m

checkType :: Context -> Term -> Term -> CanError Term
checkType ctx m t = runReaderT (runCheckType m t) ([], ctx)
  where
    runCheckType :: Term -> Term -> TypeCheck Term
    runCheckType m = return
