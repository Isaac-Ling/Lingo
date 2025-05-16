module Core.Error where
import Control.Monad.Trans

data ErrorCode
  = NoCommandLineArgsSupplied
  | InvalidCommandLineArgsSupplied
  | FailedToReadSourceFile
  | SyntaxError
  | FailedToInferType
  | TypeMismatch
  | DuplicateDefinitions
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
  show NoCommandLineArgsSupplied      = "No command line arguments supplied"
  show InvalidCommandLineArgsSupplied = "Invalid command line arguments supplied"
  show FailedToReadSourceFile         = "Failed to read source file"
  show SyntaxError                    = "Syntax error"
  show FailedToInferType              = "Failed to infer type"
  show TypeMismatch                   = "Type mismatch"
  show DuplicateDefinitions           = "Duplicate definitions"

instance Show (CanError a) where
  show (Result a)            = "Success (0)"
  show (Error errc Nothing)  = "Error (" ++ show (getErrorCode errc) ++ ") - " ++ show errc
  show (Error errc (Just s)) = "Error (" ++ show (getErrorCode errc) ++ ") - " ++ show errc ++ " - " ++ s

getErrorCode :: ErrorCode -> Int
getErrorCode NoCommandLineArgsSupplied      = 1
getErrorCode InvalidCommandLineArgsSupplied = 2
getErrorCode FailedToReadSourceFile         = 3
getErrorCode SyntaxError                    = 4
getErrorCode FailedToInferType              = 5
getErrorCode TypeMismatch                   = 6
getErrorCode DuplicateDefinitions           = 7

exitWith :: CanError a -> b
exitWith e = errorWithoutStackTrace ("Program exited with: " ++ show e)
