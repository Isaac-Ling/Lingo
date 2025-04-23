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
    Error er -> showError er
  
  -- Read source code
  source <- getSource (sourceFile args) >>= \ms -> case ms of
    Result s -> return s
    Error er -> showError er

  -- Prints lexed source for debugging
  --print (scan source)

  -- Parse
  ast <- case parse source of
    Result s -> return s
    Error er -> showError er

  -- Execute
  result <- case execute ast of
    Result a -> return a
    Error er -> showError er

  print result

parseArgs :: [String] -> CanError Args
parseArgs []     = Error NoCommandLineArgsSupplied
parseArgs (x:xs) = Result $ Args { sourceFile = x }

getSource :: FilePath -> IO (CanError ByteString)
getSource f = catch (Result <$> BS.readFile f) handler
  where
    handler :: IOException -> IO (CanError ByteString)
    handler _ = return $ Error FailedToReadSourceFile

execute :: Term -> CanError Output
execute e = case mt of
  Error er -> Error er
  Result t -> do 
    Result (Output { outTerm = eval e, outType = t })
  where
    mt = inferType [] e
