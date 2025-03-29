module Lexing.Support (Token (..)) where

data Token
  -- Variables
  = Id String
  -- Lambda abstractions
  | Backslash
  | Dot
  -- Parentheses
  | LParen
  | RParen
  -- EOF
  | EOF
  deriving (Eq, Show)
