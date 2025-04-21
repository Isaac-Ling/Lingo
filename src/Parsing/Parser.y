{
module Parsing.Parser where

import Core.Data
import Core.Error
import Lexing.Lexer
import Lexing.Tokens

import Data.Char
import Data.ByteString.Lazy.Char8 (ByteString, pack)
}

%name parser
%tokentype { PositionedToken }
%error { parseError }
%monad { Alex }
%lexer { lexer } { PositionedToken TkEOF _ }

%token
  '\\'    { PositionedToken TkBackslash _ }
  '.'     { PositionedToken TkDot _ }
  '('     { PositionedToken TkLParen _ }
  ')'     { PositionedToken TkRParen _ }
  ':='    { PositionedToken TkColonEqual _ }
  ':'     { PositionedToken TkColon _ }
  '->'    { PositionedToken TkRArrow _ }
  '*'     { PositionedToken TkStar _ }
  '0'     { PositionedToken (TkInt 0) _ }
  '1'     { PositionedToken (TkInt 1) _ }
  univ    { PositionedToken (TkUniv $$) _ }
  var     { PositionedToken (TkID $$) _ }
  int     { PositionedToken (TkInt $$) _ }

%nonassoc ':'
%nonassoc '.'
%right '->'
%nonassoc var '(' '\\'  '0' '1' 'U' '*'
%nonassoc APP

%%

Term :: { Term }
  : var          { Var $1 }
  | '0'          { Zero }
  | '1'          { One }
  | univ          { Univ $1 }
  | Abstraction  { $1 }
  | Application  { $1 }
  | PiType       { $1 }
  | '*'          { Star }
  | '(' Term ')' { $2 }

Assumption :: { Assumption }
  : var ':' Term { ($1, $3) }

Application :: { Term }
  : Term Term %prec APP { App $1 $2 }

Abstraction :: { Term }
  : '\\' '(' Assumption ')' '.' Term { Lam $3 $6 }

PiType :: { Term }
  : '(' Assumption ')' '->' Term { Pi $2 $5 }

{
parseError :: PositionedToken -> Alex a
parseError t = alexError ("Parsing error at line " ++ show (fst (ptPosition t)) ++ ", column " ++ show (snd (ptPosition t)))

lexer :: (PositionedToken -> Alex a) -> Alex a
lexer = (=<< alexMonadScan)

parse :: ByteString -> CanError Term
parse s = case runAlex s parser of
  Right t -> Result t
  Left er -> case er of
    ""     -> Error $ SyntaxError ""
    (x:xs) -> Error $ SyntaxError (toUpper x : xs)
}
