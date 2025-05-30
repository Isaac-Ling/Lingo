module Lexing.Tokens where

import Data.ByteString.Lazy.Char8 (ByteString)

data Token
  -- Identifiers
  = TkVar ByteString
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
  | TkHash
  | TkPlus
  -- Numbers
  | TkInt Int
  -- Keywords
  | TkUniv Int
  | TkInd
  | TkCheck
  -- Misc
  | TkNewL
  | TkEOF
  deriving (Eq, Show)

data PositionedToken = PositionedToken
  { ptToken    :: Token
  , ptPosition :: (Int, Int)
  } deriving (Eq, Show)
