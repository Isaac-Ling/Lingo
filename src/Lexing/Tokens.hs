module Lexing.Tokens (Token (..)) where

import Data.ByteString.Lazy.Char8 (ByteString)

data Token
  -- Identifiers
  = TkID ByteString
  -- Punctuation
  | TkBackslash
  | TkDot
  | TkColon
  | TkLParen
  | TkRParen
  -- Symbols
  | TkRArrow
  | TkColonEqual
  | TkStar
  -- Numbers
  | TkInt Integer
  -- Keywords
  | TkUniv Integer
  -- EOF
  | TkEOF
  deriving (Eq, Show)
