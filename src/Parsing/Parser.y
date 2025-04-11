{
module Parsing.Parser where

import Core.Data
import Core.Error
import Lexing.Tokens
}

%name parseExpr
%tokentype { Token }
%error { showError SyntaxError }

%token
  '0'     { Int 0 }
  '1'     { Int 1 }
  int     { Int $$ }
  '\\'    { Backslash }
  '.'     { Dot }
  '('     { LParen }
  ')'     { RParen }
  ':'     { Colon }
  '->'    { RArrow }
  '*'     { Asterisk }
  'true'  { TTrue }
  'false' { TFalse }
  'Bool'  { Boolean }
  var     { Id $$ }

%nonassoc ':'
%nonassoc '.'
%right '->'
%nonassoc var '(' '\\' '0' '1' '*' 'true' 'false' 'Bool'
%nonassoc APP

%%

Term :: { Term }
  : '*'           { Star }
  | 'true'        { Flag True }
  | 'false'       { Flag False }
  | Application   { $1 }
  | Abstraction   { $1 }
  | Term ':' Type { Anno $1 $3 }
  | var           { Var $1 }
  | '(' Term ')'  { $2 }

Application :: { Term }
  : Term Term %prec APP { App $1 $2 }

Abstraction :: { Term }
  : '\\' var ':' Type '.' Term { Lam (VarAnno $2 $4) $6 }

Type :: { Type }
  : '0'            { Zero }
  | '1'            { One }
  | 'Bool'         { Bool }
  | Type '->' Type { Arr $1 $3 }
  | '(' Type ')'   { $2 }
