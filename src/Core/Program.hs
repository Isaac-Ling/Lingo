module Core.Program (run, Option(..), Options) where

import Core.Term
import Core.Error
import Parsing.Parser
import Core.Elaboration
import Core.Judgement.Utils
import Core.Judgement.Evaluation
import Core.Judgement.Typing.Type
import Core.Judgement.Typing.Context
import IO.Source (readSource)

import Control.Monad (when)
import System.Directory (makeAbsolute)
import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString, unpack)

data Option
  = None
  | HideImplicits
  | ShowRunTime
  | WithoutK
  deriving Eq

type Options = [Option]
type Includes = [FilePath]
type SourceTypeContext = [(ByteString, SourceTerm)]

data RuntimeContext = RuntimeContext
  { rtenv :: Environment
  , rtctx :: Context
  , stctx :: SourceTypeContext
  , incs  :: [FilePath]
  }

type Runtime a = CanErrorT (ReaderT RuntimeContext IO) a

run :: Program -> FilePath -> Options -> IO (CanError ())
run p f opts = runReaderT (runCanErrorT (go p)) initRuntimeContext
  where
    initRuntimeContext = RuntimeContext { rtenv=[], rtctx=[], stctx=[], incs=[f] }

    go :: Program -> Runtime ()
    go []                      = success

    go (Def (x, m'):ds)        = do
      ctxs <- askRTCtx

      case lookup x $ rtenv ctxs of
        Just _ -> abort DuplicateDefinitions $ Just ("Duplicate definintions of " ++ unpack x ++ " found")
        _      -> success

      -- If this definition uses pattern matching, read all definitions and elaborate into an eliminator
      (m, ds') <- if isPatternMatched m'
        then do
          t' <- case lookup x $ stctx ctxs of
            Just t -> return t
            _      -> abort FailedToInferType $ Just "Missing type signature for pattern matched definition"

          let (cases, ds') = span (isSameDefinition x) ds
          let patterns = addImplicitParameters m' t' : map ((`addImplicitParameters` t') . unsafeGetDefinitionFromDeclaration) cases

          case elaboratePatternMatchedDefs x patterns t' of
            Result m     -> return (toCoreTerm m, ds')
            Error errc s -> abort errc s
        else do
          case lookup x $ stctx ctxs of
            Just t' -> return (toCoreTerm $ addImplicitParameters m' t', ds)
            _       -> return (toCoreTerm m', ds)

      case lookup x $ rtctx ctxs of
        Just t -> do
          em <- tryRun $ elaborateWithType (rtenv ctxs) (rtctx ctxs) m t
          continue (addToRTEnv (x, em)) (go ds')
        _      -> do
          (em, t) <- tryRun $ inferTypeAndElaborate (rtenv ctxs) (rtctx ctxs) m
          continue (addToRTEnv (x, em) . addToRTCtx (x, t)) (go ds')

    go (Signature (x, t'):ds)  = do
      ctxs <- askRTCtx

      let t = toCoreTerm t'
      et <- tryRun $ elaborate (rtenv ctxs) (rtctx ctxs) t
      let p = continue (addToRTCtx (x, et) . addToSourceTypeCtx (x, t')) (go ds)

      case lookup x $ rtctx ctxs of
        Just t2 -> if equal (rtenv ctxs) et t2
          then p
          else abort TypeMismatch (Just ("The type of " ++ unpack x ++ " is " ++ show t ++ " but expected " ++ show t2))
        _       -> p

    go (Pragma (Check m'):ds)  = do
      ctxs <- askRTCtx

      let m = toCoreTerm m'
      (f, t) <- tryRun $ inferTypeAndElaborate (rtenv ctxs) (rtctx ctxs) m

      let erf = eval $ unfold (rtenv ctxs) f
      let et = eval t

      liftIO $ putStrLn (showTerm f ++ " =>* " ++ showTerm erf ++ " : " ++ showTerm et)

      go ds

    go (Pragma (Type m'):ds)   = do
      ctxs <- askRTCtx

      let m = toCoreTerm m'
      (f, t) <- tryRun $ inferTypeAndElaborate (rtenv ctxs) (rtctx ctxs) m
      let et = eval t
      liftIO $ putStrLn (showTerm f ++ " : " ++ showTerm et)

      go ds

    go (Pragma (Eval m'):ds)   = do
      ctxs <- askRTCtx

      let m = toCoreTerm m'
      (f, t) <- tryRun $ inferTypeAndElaborate (rtenv ctxs) (rtctx ctxs) m
      let erf = eval $ unfold (rtenv ctxs) f
      liftIO $ putStrLn (showTerm f ++ " =>* " ++ showTerm erf)

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

        program <- case parse includeWithExtension source of
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

    abort :: ErrorCode -> Maybe String -> Runtime a
    abort errc ms = CanErrorT $ return $ Error errc ms

    addToRTEnv :: Alias -> (RuntimeContext -> RuntimeContext)
    addToRTEnv def ctxs = ctxs { rtenv=def : rtenv ctxs }

    addToRTCtx :: Assumption -> (RuntimeContext -> RuntimeContext)
    addToRTCtx sig ctxs = ctxs { rtctx=sig : rtctx ctxs }

    addToSourceTypeCtx :: (ByteString, SourceTerm) -> (RuntimeContext -> RuntimeContext)
    addToSourceTypeCtx nt ctxs = ctxs { stctx=nt : stctx ctxs }

    addToIncludes :: FilePath -> (RuntimeContext -> RuntimeContext)
    addToIncludes f ctxs = ctxs { incs=f : incs ctxs }

    showTerm :: Term -> String
    showTerm = if HideImplicits `elem` opts then showTermWithoutImplicits else show

    isSameDefinition :: ByteString -> Declaration -> Bool
    isSameDefinition b (Def (x, _)) = b == x
    isSameDefinition _ _             = False

    unsafeGetDefinitionFromDeclaration :: Declaration -> SourceTerm
    unsafeGetDefinitionFromDeclaration (Def (_, m')) = m'

instance Show Declaration where
  show (Signature (x, t')) = unpack x ++ " : " ++ show (toCoreTerm t')
  show (Def (x, m'))       = unpack x ++ " := " ++ show (toCoreTerm m')
  show (Pragma p)          = show p

instance Show Pragma where
  show (Check m')  = "#check " ++ show (toCoreTerm m')
  show (Include f) = "#include " ++ f
