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
  | TkEq
  | TkTop
  | TkBot
  -- Numbers
  | TkInt Integer
  -- Keywords
  | TkUniv Integer
  | TkInd
  | TkCheck
  | TkInr
  | TkInl
  | TkRefl
  | TkNat
  | TkSucc
  -- Misc
  | TkNewL
  | TkEOF
  deriving (Eq, Show)

data PositionedToken = PositionedToken
  { ptToken    :: Token
  , ptPosition :: (Int, Int)
  } deriving (Eq, Show)
