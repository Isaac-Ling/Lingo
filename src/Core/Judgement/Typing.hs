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
    runInferType (Univ i)        = return $ Univ (i + 1)
    runInferType Star            = return One
    runInferType Zero            = return $ Univ 0
    runInferType One             = return $ Univ 0

    runInferType (Var (Bound i)) = do
      (bctx, _) <- ask

      if i < length bctx
      then return $ bctx !! i 
      else typeError FailedToInferType (Just ("There are not " ++ show i ++ " binders to search"))
    
    runInferType (Var (Free x)) = do
      (_, ctx) <- ask

      case lookup x ctx of
        Just t  -> return t
        Nothing -> typeError FailedToInferType (Just ("Unknown variable " ++ show x))
    
    runInferType m        = return m

checkType :: Context -> Term -> Term -> CanError Term
checkType ctx m t = runReaderT (runCheckType m t) ([], ctx)
  where
    runCheckType :: Term -> Term -> TypeCheck Term
    runCheckType m = return

typeError :: ErrorCode -> Maybe String -> TypeCheck a
typeError errc ms = lift $ Error errc ms
