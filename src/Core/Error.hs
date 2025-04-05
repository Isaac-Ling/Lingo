module Core.Error where

data ErrorCode
  = Success
  | NoCommandLineArgsSupplied
  | FailedToReadSourceFile
  | TypeMismatch
  deriving Eq

data CanError a
  = Result a
  | Error ErrorCode

getErrorCode :: ErrorCode -> Int
getErrorCode Success                   = 0
getErrorCode NoCommandLineArgsSupplied = 1
getErrorCode FailedToReadSourceFile    = 1
getErrorCode TypeMismatch              = 2

instance Show ErrorCode where
  show Success                   = "Success - " ++ show (getErrorCode Success)
  show NoCommandLineArgsSupplied = "Error - " ++ show (getErrorCode NoCommandLineArgsSupplied) ++ ": No command line arguments supplied"
  show FailedToReadSourceFile    = "Error - " ++ show (getErrorCode FailedToReadSourceFile) ++ ": Failed to read source file"
  show TypeMismatch              = "Error - " ++ show (getErrorCode TypeMismatch) ++ ": Type mismatch"

showError :: ErrorCode -> a
showError er = error $ show er
