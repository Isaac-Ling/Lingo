{
module Parsing.Parser where

import Core.Data
import Core.Error
import Lexing.Tokens

import Data.ByteString.Lazy.Char8 (ByteString, pack)
}

%name parseExpr
%tokentype { Token }
%error { showError SyntaxError }

%token
  '\\'    { TkBackslash }
  '.'     { TkDot }
  '('     { TkLParen }
  ')'     { TkRParen }
  ':='    { TkColonEqual }
  ':'     { TkColon }
  '->'    { TkRArrow }
  '*'     { TkStar }
  '0'     { TkInt 0 }
  '1'     { TkInt 1 }
  'U'     { TkUniv 0 }
  var     { TkID $$ }
  int     { TkInt $$ }

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
  | 'U'          { Univ 0 }
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
