module Lexing.Tokens where

import Data.ByteString.Lazy.Char8 (ByteString)

data Token
  -- Identifiers
  = TkID ByteString
  -- Punctuation
  | TkBackslash
  | TkDot
  | TkComma
  | TkCross
  | TkColon
  | TkLParen
  | TkRParen
  | TkLSqParen
  | TkRSqParen
  -- Symbols
  | TkRArrow
  | TkColonEqual
  | TkStar
  -- Numbers
  | TkInt Integer
  -- Keywords
  | TkUniv Integer
  | TkInd
  -- EOF
  | TkEOF
  deriving (Eq, Show)

data PositionedToken = PositionedToken
  { ptToken    :: Token
  , ptPosition :: (Int, Int)
  } deriving (Eq, Show)
