module Core.Program where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Typing
import Core.Judgement.Evaluation
import IO.Source (readSource)
import Parsing.Parser

import Control.Monad (when)
import System.Directory (makeAbsolute)
import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString, unpack)

type Includes = [FilePath]

data RuntimeContext = RuntimeContext
  { env  :: Environment
  , ctx  :: Context
  , incs :: [FilePath]
  }

type Runtime a = ReaderT RuntimeContext (CanErrorT IO) a

run :: Program -> FilePath -> IO (CanError ())
run p f = runCanErrorT $ runReaderT (go p) initRuntimeContext
  where
    initRuntimeContext = RuntimeContext { env=[], ctx=[], incs=[f] }

    go :: Program -> Runtime ()
    go []                      = success

    go (Def (x, m'):ds)        = do
      ctxs <- ask

      case lookup x (env ctxs) of
        Just _ -> abort DuplicateDefinitions (Just ("Duplicate definintions of " ++ unpack x ++ " found"))
        _      -> success

      let m = toDeBruijn m'

      case lookup x (ctx ctxs) of
        Just t -> do
          let em = elaborate m t
          tryRun $ checkType (env ctxs) (ctx ctxs) em t
          local (addToEnv (x, em)) (go ds)
        _      -> do
          t <- tryRun $ inferType (env ctxs) (ctx ctxs) m
          local (addToEnv (x, m) . addToCtx (x, t)) (go ds)

    go (Signature (x, t'):ds)  = do
      ctxs <- ask

      let t = toDeBruijn t'
      tt <- tryRun $ inferType (env ctxs) (ctx ctxs) t
      let p = local (addToCtx (x, t)) (go ds)

      case lookup x (ctx ctxs) of
        Just t2 -> if equal (env ctxs) t t2
          then p
          else abort TypeMismatch (Just ("The type of " ++ unpack x ++ " is " ++ show t ++ " but expected " ++ show t2))
        _       -> p

    go (Pragma (Check m'):ds)  = do
      ctxs <- ask

      let m = toDeBruijn m'
      t <- tryRun $ inferType (env ctxs) (ctx ctxs) m
      let ert = eval $ resolve (env ctxs) m
      liftIO $ putStrLn (show m ++ " =>* " ++ show ert ++ " : " ++ show t)

      go ds

    go (Pragma (Type m'):ds)   = do
      ctxs <- ask

      let m = toDeBruijn m'
      t <- tryRun $ inferType (env ctxs) (ctx ctxs) m
      liftIO $ putStrLn (show m ++ " : " ++ show t)

      go ds

    go (Pragma (Eval m'):ds)   = do
      ctxs <- ask

      let m = toDeBruijn m'
      t <- tryRun $ inferType (env ctxs) (ctx ctxs) m
      let ert = eval $ resolve (env ctxs) m
      liftIO $ putStrLn (show m ++ " =>* " ++ show ert)

      go ds

    go (Pragma (Include f):ds) = do
      ctxs <- ask

      let includeWithExtension = f ++ ".lingo"

      file <- liftIO $ makeAbsolute includeWithExtension

      -- Ensure file has not been included already
      if file `elem` incs ctxs
      then abort CircularDependency $ Just ("Circular dependency on the file " ++ file)
      else do
        msource <- liftIO $ readSource file
        source <- case msource of
          Result s -> return s
          err      -> lift $ CanErrorT $ return err

        program <- case parse source of
          Result p -> return p
          err      -> lift $ CanErrorT $ return err

        local (addToIncludes file) (go (program ++ ds))

tryRun :: CanError a -> Runtime a
tryRun = lift . CanErrorT . return

success :: Runtime ()
success = return ()

abort :: ErrorCode -> Maybe String -> Runtime ()
abort errc ms = lift $ CanErrorT $ return $ Error errc ms

addToEnv :: Alias -> (RuntimeContext -> RuntimeContext)
addToEnv def ctxs = ctxs { env=def : env ctxs }

addToCtx :: Assumption -> (RuntimeContext -> RuntimeContext)
addToCtx sig ctxs = ctxs { ctx=sig : ctx ctxs }

addToIncludes :: FilePath -> (RuntimeContext -> RuntimeContext)
addToIncludes f ctxs = ctxs { incs=f : incs ctxs }

instance Show Declaration where
  show (Signature (x, t')) = unpack x ++ " : " ++ show (toDeBruijn t')
  show (Def (x, m'))  = unpack x ++ " := " ++ show (toDeBruijn m')
  show (Pragma p)    = show p

instance Show Pragma where
  show (Check m') = "#check " ++ show (toDeBruijn m')
  show (Include f) = "#include " ++ f
