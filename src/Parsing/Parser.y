{
module Parsing.Parser where

import Lexing.Lexer
import Lexing.Tokens
import Core.Term
import Core.Error
import Core.Program

import Data.Char
import Data.ByteString.Lazy.Char8 (ByteString, pack)
}

%name parser
%tokentype { PositionedToken }
%error { parseError }
%monad { Alex }
%lexer { lexer } { PositionedToken TkEOF _ }
--%expect 0

%token
  '\n'    { PositionedToken TkNewL _ }
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
  '->'    { PositionedToken TkRArrow _ }
  '*'     { PositionedToken TkStar _ }
  'ind'   { PositionedToken TkInd pos }
  'check' { PositionedToken TkCheck _ }
  '0'     { PositionedToken (TkInt 0) _ }
  '1'     { PositionedToken (TkInt 1) _ }
  univ    { PositionedToken (TkUniv $$) _ }
  var     { PositionedToken (TkVar $$) _ }
  int     { PositionedToken (TkInt $$) _ }

%nonassoc ':='
%nonassoc ':' '.' ','
%right '->'
%right 'x'
%nonassoc var univ '(' '[' '\\' '0' '1' 'U' '*' 'ind'
%nonassoc APP

%%

Program :: { Program }
  : Declarations { $1 }

Declarations :: { Program }
  :                         { [] }
  | '\n' Declarations       { $2 }
  | Definition Declarations { $1 : $2 }
  | Signature Declarations  { Signature $1 : $2 }
  | Pragma     Declarations { Pragma $1 : $2 }

Definition :: { Declaration }
  : var ':=' Term { Def ($1, $3) }

Signature :: { NamedAssumption }
  : var ':' Term { ($1, $3) }

Pragma :: { Pragma }
  : 'check' Term { Check $2 }

Term :: { NamedTerm }
  : '(' Term ')' { $2 }
  | var          { NVar $1 }
  | '0'          { NZero }
  | '1'          { NOne }
  | univ         { NUniv $1 }
  | Abstraction  { $1 }
  | Application  { $1 }
  | PiType       { $1 }
  | SigmaType    { $1 }
  | Pair         { $1 }
  | Induction    { $1 }
  | '*'          { NStar }

Application :: { NamedTerm }
  : Term Term %prec APP { NApp $1 $2 }

Abstraction :: { NamedTerm }
  : '\\' '(' var ':' Term ')' '.' Term { NLam ($3, Just $5) $8 }
  | '\\' var '.' Term                  { NLam ($2, Nothing) $4 }

PiType :: { NamedTerm }
  : '(' var ':' Term ')' '->' Term { NPi (Just $2, $4) $7 }
  | Term '->' Term                 { NPi (Nothing, $1) $3 }

SigmaType :: { NamedTerm }
  : '(' var ':' Term ')' 'x' Term { NSigma (Just $2, $4) $7 }
  | Term 'x' Term                 { NSigma (Nothing, $1) $3 }

Pair :: { NamedTerm }
  : '(' Term ',' Term ')' { NPair $2 $4 }

BoundTerm :: { NamedBoundTerm }
  : Term              { NNoBind $1 }
  | var '.' BoundTerm { NBind $1 $3 }

BoundTerms :: { [NamedBoundTerm] }
  :                          { [] }
  | BoundTerm                { [$1] }
  | BoundTerm ',' BoundTerms { $1 : $3 }

BoundTermsList :: { [NamedBoundTerm] }
  :                { [] }
  | ',' BoundTerms { $2 }

Induction :: { NamedTerm }
  : 'ind' '[' Term ']' '(' BoundTerm BoundTermsList ')' 
  {
    case $7 of
      []          -> outputParseError $8
      [NNoBind a] -> NInd $3 $6 [] a
      (_:xs)      -> case last xs of
        NBind _ _ -> outputParseError $8
        NNoBind a -> NInd $3 $6 (init $7) a 
      _           -> outputParseError $8
  }

{
parseError :: PositionedToken -> Alex a
parseError t = alexError ("Parsing error at line " ++ show (fst $ ptPosition t) ++ ", column " ++ show (snd $ ptPosition t))

outputParseError :: PositionedToken -> a
outputParseError t = errorWith (Error SyntaxError (Just ("Parsing error at line " ++ show (fst $ ptPosition t) ++ ", column " ++ show (snd $ ptPosition t))))

lexer :: (PositionedToken -> Alex a) -> Alex a
lexer = (=<< alexMonadScan)

parse :: ByteString -> CanError Program
parse s = case runAlex s parser of
  Right t -> Result t
  Left er -> case er of
    ""     -> Error SyntaxError Nothing
    (x:xs) -> Error SyntaxError (Just (toUpper x : xs))
}
