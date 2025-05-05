module Lingo (main) where

import Lexing.Tokens
import Core.Data
import Core.Error
import Lexing.Lexer
import Parsing.Parser
import Core.Judgement

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

run :: Program -> IO (CanError ())
run = runWithContexts [] []
  where
    runWithContexts :: Environment -> Context -> Program -> IO (CanError ())
    runWithContexts e g []     = return (Result ())
    runWithContexts e g (d:ds) = case d of
        Def (x, m)       -> case typeCheck g m of
          Result t    -> case lookup x g of
            Nothing -> p
            Just t' -> if t == t' then p else return (Error TypeMismatch (Just ("The type of " ++ unpack x ++ " is " ++ show t ++ " but expected " ++ show t')))
            where p = runWithContexts ((x, unsafeEval e m) : e) ((x, t) : g) ds
          Error err s -> return (Error err s)
        Anno (x, t)      -> case lookup x g of
          Nothing -> p
          Just t' -> if t == t' then p else return (Error TypeMismatch (Just ("The type of " ++ unpack x ++ " is " ++ show t' ++ " but expected " ++ show t)))
          where p = runWithContexts e ((x, t) : g) ds
        Pragma (Check m) -> do
          case typeCheck g m of
            Result t    -> do
              putStrLn (show m ++ " := " ++ show (unsafeEval e m) ++ " : " ++ show t)
              runWithContexts e g ds
            Error err s -> return (Error err s)

instance Show Pragma where
  show (Check m) = "#check " ++ show m

instance Show Declaration where
  show (Anno (x, t)) = unpack x ++ " : " ++ show t
  show (Def (x, m))  = unpack x ++ " := " ++ show m
  show (Pragma p)    = show p
