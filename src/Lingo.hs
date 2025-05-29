module Lingo (main) where

import Core.Error
import IO.Args
import IO.Source
import Core.Program ( run )
import Parsing.Parser ( parse )

import System.Environment (getArgs)

main :: IO ()
main = do
  -- Get command line args
  rawArgs <- getArgs
  args <- case parseArgs rawArgs of
    Result a -> return a
    err      -> exitWith err

  case args of
    Source f -> runFile f
    Help     -> showHelp

runFile :: FilePath -> IO ()
runFile s = do
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
  result <- run program

  -- Output result
  exitWith result

showHelp :: IO ()
showHelp = do
  putStrLn "Run Lingo with the following arguments:\n\
  \  <filename>.lingo - Executes the given Lingo program\n\
  \  -h               - Displays help information"
  exitWith (Result ())
