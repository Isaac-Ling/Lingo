{
module Parsing.Parser where

import Core.Data
import Core.Error
import Core.Evaluation
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
%expect 0

%token
  '\\'    { PositionedToken TkBackslash _ }
  '.'     { PositionedToken TkDot _ }
  ','     { PositionedToken TkComma _ }
  'x'     { PositionedToken TkCross _ }
  '('     { PositionedToken TkLParen _ }
  ')'     { PositionedToken TkRParen _ }
  '['     { PositionedToken TkLSqParen _ }
  ']'     { PositionedToken TkRSqParen _ }
  ':='    { PositionedToken TkColonEqual _ }
  ':'     { PositionedToken TkColon _ }
  ';'     { PositionedToken TkSemiColon _ }
  '->'    { PositionedToken TkRArrow _ }
  '*'     { PositionedToken TkStar _ }
  'ind'   { PositionedToken TkInd _ }
  '0'     { PositionedToken (TkInt 0) _ }
  '1'     { PositionedToken (TkInt 1) _ }
  univ    { PositionedToken (TkUniv $$) _ }
  var     { PositionedToken (TkID $$) _ }
  int     { PositionedToken (TkInt $$) _ }

%nonassoc ':='
%nonassoc ':' '.' ','
%right '->'
%nonassoc var univ '(' '[' '\\' '0' '1' 'U' '*' 'x' 'ind'
%nonassoc APP

%%

Program :: { Program }
  : Declarations { reverse $1 }

Declarations :: { Program }
  :                    { [] }
  | Definition Program { $1 : $2 }
  | Assumption Program { (Anno $1) : $2 }

Definition :: { Declaration }
  : var ':=' Term { Def ($1, $3) }

Term :: { Term }
  : var          { Var $1 }
  | '0'          { Zero }
  | '1'          { One }
  | univ         { Univ $1 }
  | Abstraction  { $1 }
  | Application  { $1 }
  | PiType       { $1 }
  | SigmaType    { $1 }
  | Pair         { $1 }
  | Induction    { $1 }
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
  | Term '->' Term               { Pi (getFreshVar $3, $1) $3 }

SigmaType :: { Term }
  : '(' Assumption ')' 'x' Term { Sigma $2 $5 }
  | Term 'x' Term               { Sigma (getFreshVar $3, $1) $3 }

Pair :: { Term }
  : '(' Term ',' Term ')' { Pair $2 $4 }

BoundTerm :: { BoundTerm }
  : Term              { NoBind $1 }
  | var '.' BoundTerm { Bind $1 $3 }

BoundTerms :: { [BoundTerm] }
  :                          { [] }
  | BoundTerm                { [$1] }
  | BoundTerm ',' BoundTerms { $1 : $3 }

BoundTermsList :: { [BoundTerm] }
  :                { [] }
  | ',' BoundTerms { $2 }

Induction :: { Term }
  : 'ind' '[' Term ']' '(' BoundTerm BoundTermsList ';' Term ')' { Ind $3 $6 $7 $9 }

{
parseError :: PositionedToken -> Alex a
parseError t = alexError ("Parsing error at line " ++ show (fst (ptPosition t)) ++ ", column " ++ show (snd (ptPosition t)))

lexer :: (PositionedToken -> Alex a) -> Alex a
lexer = (=<< alexMonadScan)

parse :: ByteString -> CanError Program
parse s = case runAlex s parser of
  Right t -> Result t
  Left er -> case er of
    ""     -> Error SyntaxError Nothing
    (x:xs) -> Error SyntaxError (Just (toUpper x : xs))
}
