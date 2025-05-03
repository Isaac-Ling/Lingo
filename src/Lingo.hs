module Lingo (main) where

import Lexing.Tokens
import Core.Data
import Core.Error
import Lexing.Lexer
import Parsing.Parser
import Core.Judgement
import Core.Evaluation

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

  print $ scan source

  -- Parse
  program <- case parse source of
    Result s -> return s
    err      -> outputError err

  print program

  -- Run
  result <- case run program of
    Result a -> return (Result a)
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

run :: Program -> CanError ()
run = runWithContexts [] []
  where
    runWithContexts :: Environment -> Context -> Program -> CanError ()
    runWithContexts e g []     = Result ()
    runWithContexts e g (d:ds) = case d of
        Def (x, m) -> case typeCheck g m of
          Error err s -> Error err s
          Result t    -> case lookup x g of
            Nothing -> p
            Just t' -> if t == t' then p else Error TypeMismatch (Just ("The type of " ++ unpack x ++ " is " ++ show t ++ " but expected " ++ show t'))
            where p = runWithContexts ((x, eval e m) : e) g ds
        --Anno m t      -> 

instance Show Declaration where
  show (Anno (x, t)) = unpack x ++ " : " ++ show t
  show (Def (x, m))  = unpack x ++ " := " ++ show m
