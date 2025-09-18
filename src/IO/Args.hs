module IO.Args where

import Core.Error

data Argument
  = Source FilePath
  | ArgHideImplicits
  | Help

type Args = [Argument]

parseArgs :: [String] -> CanError Args
parseArgs []              = return []
parseArgs (a:as)          = do
  arg  <- parseArg a
  args <- parseArgs as
  return $ arg : args
  where
    parseArg :: String -> CanError Argument
    parseArg ['-', c]    = case c of
      'h' -> return Help
      _   -> Error InvalidCommandLineArgsProvided Nothing
    parseArg ('-':'-':c) = case c of
      "help"          -> return Help
      "hideImplicits" -> return ArgHideImplicits
      _      -> Error InvalidCommandLineArgsProvided Nothing
    parseArg s           = return $ Source s
