module Core.Error where

data ErrorCode
  = Success
  | TypeMismatch

data CanError a
  = Result a
  | Error ErrorCode

getErrorCode :: ErrorCode -> Int
getErrorCode TypeMismatch = 0

getErrorMessage :: ErrorCode -> String
getErrorMessage TypeMismatch = "Error - " ++ show (getErrorCode TypeMismatch) ++ ": Type Mismatch"
