{
module Parsing.Parser where

import Lexing.Tokens
import Parsing.Syntax
}

%name parseExpr
%tokentype { Token }
%error { parseError }

%token
  var  { Id $$ }
  '\\' { Backslash }
  '.'  { Dot }
  '('  { LParen }
  ')'  { RParen }

%nonassoc var '(' '\\'
%nonassoc APP

%%

Term :: { Term }
  : var          { Var $1 }
  | Expr         { $1 }
  | '(' Expr ')' { $2 }

Expr :: { Term }
  : Abstraction { $1 }
  | Application { $1 }

Abstraction :: { Term }
  : '\\' var '.' Term { Lam $2 $4 }

Application :: { Term }
  : Term Term %prec APP { App $1 $2 }

{
  parseError = error . show
}
