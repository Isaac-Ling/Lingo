module Core.Error where

data ErrorCode
  = Success
  | NoCommandLineArgsSupplied
  | FailedToReadSourceFile
  | SyntaxError String
  | FailedToInferType
  | TypeMismatch
  deriving Eq

data CanError a
  = Result a
  | Error ErrorCode

getErrorCode :: ErrorCode -> Int
getErrorCode Success                   = 0
getErrorCode NoCommandLineArgsSupplied = 1
getErrorCode FailedToReadSourceFile    = 2
getErrorCode (SyntaxError _)           = 3
getErrorCode FailedToInferType         = 4
getErrorCode TypeMismatch              = 5

instance Show ErrorCode where
  show Success                   = "Success - " ++ show (getErrorCode Success)
  show NoCommandLineArgsSupplied = "Error - " ++ show (getErrorCode NoCommandLineArgsSupplied) ++ " - No command line arguments supplied"
  show FailedToReadSourceFile    = "Error - " ++ show (getErrorCode FailedToReadSourceFile) ++ " - Failed to read source file"
  show (SyntaxError s)           = "Error - " ++ show (getErrorCode $ SyntaxError s) ++ " - " ++ s
  show FailedToInferType         = "Error - " ++ show (getErrorCode FailedToInferType) ++ " - Failed to infer type"
  show TypeMismatch              = "Error - " ++ show (getErrorCode TypeMismatch) ++ " - Type mismatch"

showError :: ErrorCode -> a
showError er = error $ show er
