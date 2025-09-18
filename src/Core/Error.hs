module Core.Error where

import Control.Monad.Trans
import qualified System.Exit as Sys ( ExitCode(ExitFailure), exitWith, exitSuccess)

data ErrorCode
  = NoCommandLineArgsProvided
  | InvalidCommandLineArgsProvided
  | FailedToReadSourceFile
  | SyntaxError
  | FailedToInferType
  | TypeMismatch
  | DuplicateDefinitions
  | CircularDependency
  | UnificationError
  deriving Eq

data CanError a
  = Result a
  | Error ErrorCode (Maybe String)
  deriving Eq

instance Functor CanError where
  fmap f (Result t)     = Result (f t)
  fmap f (Error errc s) = Error errc s

instance Applicative CanError where
  pure                                = Result
  (Result f) <*> (Result t)           = Result (f t)
  (Error errc s) <*> _                = Error errc s
  _ <*> (Error errc s)                = Error errc s

instance Monad CanError where
  (Result t) >>= f     = f t
  (Error errc s) >>= _ = Error errc s
  return = pure

newtype CanErrorT m a = CanErrorT { runCanErrorT :: m (CanError a) }

instance Monad m => Functor (CanErrorT m) where
  fmap f (CanErrorT mca) = CanErrorT (fmap (fmap f) mca)

instance Monad m => Applicative (CanErrorT m) where
  pure x                          = CanErrorT (pure $ pure x)
  CanErrorT mcf <*> CanErrorT mca = CanErrorT $ do
    cf <- mcf
    ca <- mca
    return (cf <*> ca)

instance Monad m => Monad (CanErrorT m) where
  return              = pure
  CanErrorT mca >>= f = CanErrorT $ do
    ca <- mca
    case ca of
      Result a     -> runCanErrorT $ f a
      Error errc s -> return $ Error errc s

instance MonadTrans CanErrorT where
  lift ma = CanErrorT $ do
    return <$> ma

instance MonadIO m => MonadIO (CanErrorT m) where
  liftIO io = CanErrorT (liftIO (Result <$> io))

instance Show ErrorCode where
  show NoCommandLineArgsProvided      = "No command line arguments provided"
  show InvalidCommandLineArgsProvided = "Invalid command line arguments provided"
  show FailedToReadSourceFile         = "Failed to read source file"
  show SyntaxError                    = "Syntax error"
  show FailedToInferType              = "Failed to infer type"
  show TypeMismatch                   = "Type mismatch"
  show DuplicateDefinitions           = "Duplicate definitions"
  show CircularDependency             = "Circular dependency"
  show UnificationError               = "Unification Error"

instance Show (CanError a) where
  show (Result a)            = "Success (0)"
  show (Error errc Nothing)  = "Error (" ++ show (getErrorCode errc) ++ ") - " ++ show errc
  show (Error errc (Just s)) = "Error (" ++ show (getErrorCode errc) ++ ") - " ++ show errc ++ " - " ++ s

getErrorCode :: ErrorCode -> Int
getErrorCode NoCommandLineArgsProvided      = 1
getErrorCode InvalidCommandLineArgsProvided = 2
getErrorCode FailedToReadSourceFile         = 3
getErrorCode SyntaxError                    = 4
getErrorCode FailedToInferType              = 5
getErrorCode TypeMismatch                   = 6
getErrorCode DuplicateDefinitions           = 7
getErrorCode CircularDependency             = 8
getErrorCode UnificationError               = 9

errorWith :: CanError a -> b
errorWith e = errorWithoutStackTrace ("Program exited with: " ++ show e)

exitWith :: CanError a -> IO b
exitWith (Result a) = do
  putStrLn ("Program exited with: " ++ show (Result a))
  Sys.exitSuccess
exitWith (Error errc s)          = do
  putStrLn ("Program exited with: " ++ show (Error errc s))
  Sys.exitWith $ Sys.ExitFailure $ getErrorCode errc
