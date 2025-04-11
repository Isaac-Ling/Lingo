module Lexing.Tokens (Token (..)) where

import Data.ByteString.Lazy.Char8 (ByteString)

data Token
  -- Variables
  = Id ByteString
  -- Lambda abstractions
  | Backslash
  | Dot
  -- Types
  | Colon
  | RArrow
  | Boolean
  -- Parentheses
  | LParen
  | RParen
  -- Booleans
  | TTrue
  | TFalse
  -- Numbers
  | Int Integer
  -- Other
  | Asterisk
  -- EOF
  | EOF
  deriving (Eq, Show)
