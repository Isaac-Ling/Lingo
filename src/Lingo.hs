module Lingo (main) where

import Core.Error
import IO.Args
import IO.Source
import Core.Program
import Parsing.Parser (parse)
import System.Directory (makeAbsolute)

import System.Environment (getArgs)

main :: IO ()
main = do
  -- Get command line args
  rawArgs <- getArgs
  args <- case parseArgs rawArgs of
    Result a -> return a
    err      -> exitWith err

  executeArgs args

executeArgs :: Args -> IO ()
executeArgs []   = exitWith $ Error NoCommandLineArgsProvided Nothing
executeArgs args = go args [] Nothing
  where
    go :: Args -> Options -> Maybe FilePath -> IO ()
    go args opts mf = case args of
      []                   -> case mf of
        Just f -> runFile f opts
        _      -> exitWith $ Error InvalidCommandLineArgsProvided $ Just "No source file provided"
      [Help]               -> showHelp
      (Source f:as)        -> case mf of 
        Just _ -> exitWith $ Error InvalidCommandLineArgsProvided $ Just "Multiple source files provided"
        _      -> go as opts $ Just f
      (ArgHideImplicits:as) -> go as (HideImplicits : opts) mf

runFile :: FilePath -> Options -> IO ()
runFile s opts = do
  -- Read source
  msource <- readSource s
  source <- case msource of
    Result s -> return s
    err      -> exitWith err

  -- Parse
  program <- case parse source of
    Result p -> return p
    err      -> exitWith err

  -- Run
  file <- makeAbsolute s
  result <- run program file opts

  -- Output result
  exitWith result

showHelp :: IO ()
showHelp = do
  putStrLn "Run Lingo with the following arguments:\n\
  \  <filename>.lingo - Executes the given Lingo program\n\
  \  -h               - Displays help information"
  exitWith (Result ())
