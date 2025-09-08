module Core.Program where

import Core.Term
import Core.Error
import Parsing.Parser
import Core.Judgement.Utils
import Core.Judgement.Evaluation
import Core.Judgement.Typing.Type
import Core.Judgement.Typing.Context
import IO.Source (readSource)

import Control.Monad (when)
import System.Directory (makeAbsolute)
import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString, unpack)

type Includes = [FilePath]

type NamedTypeContext = [(ByteString, SourceTerm)]

data RuntimeContext = RuntimeContext
  { rtenv :: Environment
  , rtctx :: Context
  , ntctx :: NamedTypeContext
  , incs  :: [FilePath]
  }

type Runtime a = CanErrorT (ReaderT RuntimeContext IO) a

run :: Program -> FilePath -> IO (CanError ())
run p f = runReaderT (runCanErrorT (go p)) initRuntimeContext
  where
    initRuntimeContext = RuntimeContext { rtenv=[], rtctx=[], ntctx=[], incs=[f] }

    go :: Program -> Runtime ()
    go []                      = success

    go (Def (x, m'):ds)        = do
      ctxs <- askRTCtx

      case lookup x $ rtenv ctxs of
        Just _ -> abort DuplicateDefinitions (Just ("Duplicate definintions of " ++ unpack x ++ " found"))
        _      -> success

      let m = case lookup x $ ntctx ctxs of
                Just t' -> toDeBruijn $ elaborate m' t'
                _       -> toDeBruijn m'

      case lookup x $ rtctx ctxs of
        Just t -> do
          (em, _) <- tryRun $ checkType (rtenv ctxs) (rtctx ctxs) m t
          continue (addToRTEnv (x, em)) (go ds)
        _      -> do
          (em, t) <- tryRun $ inferType (rtenv ctxs) (rtctx ctxs) m
          continue (addToRTEnv (x, em) . addToRTCtx (x, t)) (go ds)

    go (Signature (x, t'):ds)  = do
      ctxs <- askRTCtx

      let t = toDeBruijn t'
      (et, _) <- tryRun $ inferType (rtenv ctxs) (rtctx ctxs) t
      let p = continue (addToRTCtx (x, et) . addToNamedTypeCtx (x, t')) (go ds)

      case lookup x $ rtctx ctxs of
        Just t2 -> if equal (rtenv ctxs) t t2
          then p
          else abort TypeMismatch (Just ("The type of " ++ unpack x ++ " is " ++ show t ++ " but expected " ++ show t2))
        _       -> p

    go (Pragma (Check m'):ds)  = do
      ctxs <- askRTCtx

      let m = toDeBruijn m'
      (f, t) <- tryRun $ inferType (rtenv ctxs) (rtctx ctxs) m

      let erf = eval $ resolve (rtenv ctxs) f
      let et = eval t
      liftIO $ putStrLn (show f ++ " =>* " ++ show erf ++ " : " ++ show et)

      go ds

    go (Pragma (Type m'):ds)   = do
      ctxs <- askRTCtx

      let m = toDeBruijn m'
      (f, t) <- tryRun $ inferType (rtenv ctxs) (rtctx ctxs) m
      let et = eval t
      liftIO $ putStrLn (show f ++ " : " ++ show et)

      go ds

    go (Pragma (Eval m'):ds)   = do
      ctxs <- askRTCtx

      let m = toDeBruijn m'
      (f, t) <- tryRun $ inferType (rtenv ctxs) (rtctx ctxs) m
      let erf = eval $ resolve (rtenv ctxs) f
      liftIO $ putStrLn (show f ++ " =>* " ++ show erf)

      go ds

    go (Pragma (Include f):ds) = do
      ctxs <- askRTCtx

      let includeWithExtension = f ++ ".lingo"

      file <- liftIO $ makeAbsolute includeWithExtension

      -- Ensure file has not been included already
      if file `elem` incs ctxs
      then abort CircularDependency $ Just ("Circular dependency on the file " ++ file)
      else do
        msource <- liftIO $ readSource file
        source <- case msource of
          Result s -> return s
          err      -> CanErrorT $ return err

        program <- case parse source of
          Result p -> return p
          err      -> CanErrorT $ return err

        continue (addToIncludes file) (go (program ++ ds))

tryRun :: CanError a -> Runtime a
tryRun = CanErrorT . return

success :: Runtime ()
success = return ()

askRTCtx :: Runtime RuntimeContext
askRTCtx = lift ask

continue :: (RuntimeContext -> RuntimeContext) -> Runtime () -> Runtime ()
continue f m = CanErrorT $ local f $ runCanErrorT m

abort :: ErrorCode -> Maybe String -> Runtime ()
abort errc ms = CanErrorT $ return $ Error errc ms

addToRTEnv :: Alias -> (RuntimeContext -> RuntimeContext)
addToRTEnv def ctxs = ctxs { rtenv=def : rtenv ctxs }

addToRTCtx :: Assumption -> (RuntimeContext -> RuntimeContext)
addToRTCtx sig ctxs = ctxs { rtctx=sig : rtctx ctxs }

addToNamedTypeCtx :: (ByteString, SourceTerm) -> (RuntimeContext -> RuntimeContext)
addToNamedTypeCtx nt ctxs = ctxs { ntctx=nt : ntctx ctxs }

addToIncludes :: FilePath -> (RuntimeContext -> RuntimeContext)
addToIncludes f ctxs = ctxs { incs=f : incs ctxs }

instance Show Declaration where
  show (Signature (x, t')) = unpack x ++ " : " ++ show (toDeBruijn t')
  show (Def (x, m'))       = unpack x ++ " := " ++ show (toDeBruijn m')
  show (Pragma p)          = show p

instance Show Pragma where
  show (Check m')  = "#check " ++ show (toDeBruijn m')
  show (Include f) = "#include " ++ f
