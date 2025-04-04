module Lingo (main) where

import Lexing.Lexer
import Lexing.Tokens
import Parsing.Parser
import Core.Data
import Core.Evaluation

import Data.ByteString.Lazy.Char8 (ByteString)
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
    Nothing -> error "Error: Missing required arguments"
    Just a  -> return a
  
  -- Read source code
  source <- getSource (sourceFile args) >>= \ms -> case ms of
    Nothing -> error "Error: Invalid source file"
    Just s  -> return s

  -- Lexing
  let tokens = alexScanTokens source

  -- Parsing
  let ast = parseExpr tokens

  -- Evaluation
  let result = eval ast

  -- Output
  print ast
  print result

parseArgs :: [String] -> Maybe Args
parseArgs []     = Nothing
parseArgs (x:xs) = Just (Args { sourceFile = x })

getSource :: FilePath -> IO (Maybe ByteString)
getSource f = catch (Just <$> BS.readFile f) handler
  where
    handler :: IOException -> IO (Maybe ByteString)
    handler _ = return Nothing
