module Core.Error where

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
