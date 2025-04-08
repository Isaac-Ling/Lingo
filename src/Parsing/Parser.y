{
module Parsing.Parser where

import Core.Data
import Lexing.Tokens
}

%name parseExpr
%tokentype { Token }
%error { parseError }

%token
  var  { Id $$ }
  '0'  { Int 0 }
  '1'  { Int 1 }
  int  { Int $$ }
  '\\' { Backslash }
  '.'  { Dot }
  '('  { LParen }
  ')'  { RParen }
  ':'  { Colon }
  '->' { RArrow }
  '*'  { Asterisk }

%nonassoc ':'
%nonassoc '.'
%right '->'
%nonassoc var '(' '\\' '0' '1' '*'
%nonassoc APP

%%

Term :: { Term }
  : var           { Var $1 }
  | '*'           { Star }
  | Application   { $1 }
  | Abstraction   { $1 }
  | Term ':' Type { Anno $1 $3}
  | '(' Term ')'  { $2 }

Application :: { Term }
  : Term Term %prec APP { App $1 $2 }

Abstraction :: { Term }
  : '\\' var ':' Type '.' Term { Lam (VarAnno $2 $4) $6 }

Type :: { Type }
  : '0'            { Zero }
  | '1'            { One }
  | Type '->' Type { Arr $1 $3 }
  | '(' Type ')'   { $2 }

{
  parseError = error . show
}
