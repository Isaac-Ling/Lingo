module Lingo (main) where

import Lexing.Lexer
import Lexing.Tokens
import Parsing.Parser
import Core.Data
import Core.Error
import Core.Evaluation
import Core.TypeChecking

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
    Result a -> return a
    Error er -> showError er
  
  -- Read source code
  source <- getSource (sourceFile args) >>= \ms -> case ms of
    Result s -> return s
    Error er -> showError er

  -- Lex
  let tokens = alexScanTokens source

  -- Parse
  let ast = parseExpr tokens

  -- Execute
  result <- execute ast >>= \mr -> case mr of
    Result a -> return a
    Error er -> showError er

  print (show (fst result) ++ " : " ++ show (snd result))

parseArgs :: [String] -> CanError Args
parseArgs []     = Error NoCommandLineArgsSupplied
parseArgs (x:xs) = Result $ Args { sourceFile = x }

getSource :: FilePath -> IO (CanError ByteString)
getSource f = catch (Result <$> BS.readFile f) handler
  where
    handler :: IOException -> IO (CanError ByteString)
    handler _ = return (Error FailedToReadSourceFile)

execute :: Term -> IO (CanError (Term, Term))
execute e = case mt of
  Error er -> return (Error er)
  Result t -> do 
    return (Result (eval e, t))
  where
    mt = typeCheck e
