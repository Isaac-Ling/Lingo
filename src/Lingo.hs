module Lingo (main) where

import Lexing.Tokens
import Core.Data
import Core.Error
import Lexing.Lexer
import Parsing.Parser
import Core.Judgement
import Core.Execution

import Data.ByteString.Lazy.Char8 (ByteString, unpack)
import qualified Data.ByteString.Lazy.Char8 as BS
import System.Environment (getArgs)
import Control.Exception (catch, IOException)

data Args = Args
  { sourceFile :: FilePath
  }

main :: IO ()
main = do
  -- Get command line args
  args <- getArgs >>= \ma -> case parseArgs ma of
    Result a -> return a
    err      -> outputError err
  
  -- Read source code
  source <- getSource (sourceFile args) >>= \ms -> case ms of
    Result s -> return s
    err      -> outputError err

  -- Parse
  program <- case parse source of
    Result s -> return s
    err      -> outputError err

  --putStrLn $ unlines $ map show program

  -- Run
  result <- run program >>= \mr -> case mr of
    Result a -> return (Result a)
    err      -> outputError err

  putStrLn ("Program exited with: " ++ show result)

parseArgs :: [String] -> CanError Args
parseArgs []     = Error NoCommandLineArgsSupplied Nothing
parseArgs (x:xs) = Result $ Args { sourceFile = x }

getSource :: FilePath -> IO (CanError ByteString)
getSource f = catch (Result <$> BS.readFile f) handler
  where
    handler :: IOException -> IO (CanError ByteString)
    handler _ = return $ Error FailedToReadSourceFile Nothing
