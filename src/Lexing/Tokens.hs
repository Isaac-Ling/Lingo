module Lexing.Tokens where

import Data.ByteString.Lazy.Char8 (ByteString)

data Token
  -- Identifiers
  = TkVar ByteString
  -- Strings
  | TkString ByteString
  -- Punctuation
  | TkBackslash
  | TkDot
  | TkComma
  | TkCross
  | TkColon
  | TkLParen
  | TkRParen
  | TkLCurlyParen
  | TkRCurlyParen
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
  | TkType
  | TkEval
  | TkInclude
  | TkInr
  | TkInl
  | TkRefl
  | TkNat
  | TkSucc
  | TkFunext
  | TkUnivalence
  -- Misc
  | TkNewL
  | TkEOF
  deriving (Eq, Show)

data PositionedToken = PositionedToken
  { ptToken    :: Token
  , ptPosition :: (Int, Int)
  } deriving (Eq, Show)
