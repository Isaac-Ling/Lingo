module Lingo (main) where

import Lexing.Tokens
import Core.Data
import Core.Error
import Lexing.Lexer
import Parsing.Parser
import Core.Judgement
import Core.Evaluation

import Data.ByteString.Lazy.Char8 (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
import System.Environment (getArgs)
import Control.Exception (catch, IOException)

data Args = Args
  { sourceFile :: FilePath
  }

data Output = Output
  { outTerm :: Term
  , outType :: Term
  }

instance Show Output where
  show (Output { outTerm = m, outType = t }) = show m ++ " : " ++ show t

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

  -- Prints lexed source for debugging
  --print (scan source)

  -- Parse
  ast <- case parse source of
    Result s -> return s
    err      -> outputError err

  --print ast

  -- Execute
  result <- case execute ast of
    Result a -> return a
    err      -> outputError err

  print result

parseArgs :: [String] -> CanError Args
parseArgs []     = Error NoCommandLineArgsSupplied Nothing
parseArgs (x:xs) = Result $ Args { sourceFile = x }

getSource :: FilePath -> IO (CanError ByteString)
getSource f = catch (Result <$> BS.readFile f) handler
  where
    handler :: IOException -> IO (CanError ByteString)
    handler _ = return $ Error FailedToReadSourceFile Nothing

execute :: Term -> CanError Output
execute e = case mt of
  Error err s -> Error err s
  Result t    -> do 
    Result (Output { outTerm = eval e, outType = t })
  where
    mt = typeCheck [] e
