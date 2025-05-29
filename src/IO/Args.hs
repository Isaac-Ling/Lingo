module IO.Args where

import Core.Error

data Args
  = Source FilePath
  | Help

parseArgs :: [String] -> CanError Args
parseArgs []         = Error NoCommandLineArgsSupplied Nothing
parseArgs [['-', c]] = case c of
  'h' -> Result Help
  _   -> Error InvalidCommandLineArgsSupplied Nothing
parseArgs [s]        = Result $ Source s
parseArgs _          = Error InvalidCommandLineArgsSupplied Nothing
