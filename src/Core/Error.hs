module Core.Error where

data ErrorCode
  = Success
  | NoCommandLineArgsSupplied
  | FailedToReadSourceFile
  | SyntaxError
  | FailedToInferType
  | TypeMismatch
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
  show Success                   = "Success"
  show NoCommandLineArgsSupplied = "No command line arguments supplied"
  show FailedToReadSourceFile    = "Failed to read source file"
  show SyntaxError               = "Syntax error"
  show FailedToInferType         = "Failed to infer type"
  show TypeMismatch              = "Type mismatch"

instance Show (CanError a) where
  show (Result a)            = "Success (" ++ show (getErrorCode Success) ++ ")"
  show (Error errc Nothing)  = "Error (" ++ show (getErrorCode errc) ++ ") - " ++ show errc
  show (Error errc (Just s)) = "Error (" ++ show (getErrorCode errc) ++ ") - " ++ show errc ++ " - " ++ s

getErrorCode :: ErrorCode -> Int
getErrorCode Success                   = 0
getErrorCode NoCommandLineArgsSupplied = 1
getErrorCode FailedToReadSourceFile    = 2
getErrorCode SyntaxError               = 3
getErrorCode FailedToInferType         = 4
getErrorCode TypeMismatch              = 5

outputError :: CanError a -> b
outputError = error . show
