module Lingo (main) where

import Lexing.Lexer
import Lexing.Support
import System.Environment

main :: IO ()
main = do
  args <- getArgs
  if null args then 
    error "Error: No file provided" 
  else 
    print (alexScanTokens (head args))
