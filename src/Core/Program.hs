module Core.Program where

import Core.Term
import Core.Error
import Core.Judgement

import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString, unpack)

newtype Pragma
  = Check Term

data Declaration
  = Def Alias
  | Signature Assumption
  | Pragma Pragma

type Program = [Declaration]

-- TODO: Use IO in runtime to print out #checks
type Runtime a = ReaderT (Environment, Context) (CanErrorT IO) a

run :: Program -> IO (CanError ())
run p = runCanErrorT $ runReaderT (runProgram p) ([], [])
  where
    runProgram :: Program -> Runtime ()
    runProgram []                    = success

    runProgram (Def (x, m):ds)       = do
      (env, ctx) <- ask

      case lookup x env of
        Just _ -> abort DuplicateDefinitions (Just ("Duplicate definintions of " ++ unpack x ++ " found"))
        _      -> success

      t <- case lookup x ctx of
        Just t -> tryRun $ checkType env ctx m t
        _      -> tryRun $ inferType env ctx m

      local (addToRuntime (x, m) (x, t)) (runProgram ds)

    runProgram (Signature (x, t):ds) = do
      (env, ctx) <- ask
      
      let p = local (addToCtx (x, t)) (runProgram ds)

      case lookup x ctx of
        Just t' -> if t === t' $ env 
          then p 
          else abort TypeMismatch (Just ("The type of " ++ unpack x ++ " is " ++ show t' ++ " but expected " ++ show t))
        _       -> p
      
    runProgram (Pragma (Check m):ds) = do
      (env, ctx) <- ask
      
      case inferType env ctx m of
        Result t     -> liftIO $ putStrLn (show m ++ " : " ++ show t)
        Error errc s -> abort errc s

      runProgram ds

tryRun :: CanError a -> Runtime a
tryRun = lift . CanErrorT . return

success :: Runtime ()
success = return ()

abort :: ErrorCode -> Maybe String -> Runtime ()
abort errc ms = lift $ CanErrorT $ return $ Error errc ms

addToEnv :: Alias -> ((Environment, Context) -> (Environment, Context))
addToEnv def (env, ctx) = (def : env, ctx)

addToCtx :: Assumption -> ((Environment, Context) -> (Environment, Context))
addToCtx sig (env, ctx) = (env, sig : ctx)

addToRuntime :: Alias -> Assumption -> ((Environment, Context) -> (Environment, Context))
addToRuntime def sig = addToCtx sig . addToEnv def

instance Show Declaration where
  show (Signature (x, t)) = unpack x ++ " : " ++ show t
  show (Def (x, m))  = unpack x ++ " := " ++ show m
  show (Pragma p)    = show p

instance Show Pragma where
  show (Check m) = "#check " ++ show m
