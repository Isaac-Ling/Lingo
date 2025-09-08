{
module Parsing.Parser where

import Lexing.Lexer
import Lexing.Tokens
import Core.Term
import Core.Error

import Data.Char
import Data.ByteString.Lazy.Char8 (ByteString, pack, unpack)
}

%name parser
%tokentype { PositionedToken }
%error { parseError }
%monad { Alex }
%lexer { lexer } { PositionedToken TkEOF _ }
--%expect 0

%token
  '\n'     { PositionedToken TkNewL _ }
  '\\'     { PositionedToken TkBackslash _ }
  '.'      { PositionedToken TkDot _ }
  ','      { PositionedToken TkComma _ }
  'x'      { PositionedToken TkCross _ }
  '+'      { PositionedToken TkPlus _ }
  '('      { PositionedToken TkLParen _ }
  ')'      { PositionedToken TkRParen _ }
  '{'      { PositionedToken TkLCurlyParen _ }
  '}'      { PositionedToken TkRCurlyParen _ }
  '['      { PositionedToken TkLSqParen _ }
  ']'      { PositionedToken TkRSqParen _ }
  ':='     { PositionedToken TkColonEqual _ }
  ':'      { PositionedToken TkColon _ }
  '='      { PositionedToken TkEq _ }
  '->'     { PositionedToken TkRArrow _ }
  '*'      { PositionedToken TkStar _ }
  'ind'    { PositionedToken TkInd pos }
  'check'  { PositionedToken TkCheck _ }
  'type'   { PositionedToken TkType _ }
  'eval'   { PositionedToken TkEval _ }
  'include'{ PositionedToken TkInclude _ }
  'inl'    { PositionedToken TkInl _ }
  'inr'    { PositionedToken TkInr _ }
  'refl'   { PositionedToken TkRefl _ }
  'Nat'    { PositionedToken TkNat _ }
  'succ'   { PositionedToken TkSucc _ }
  'funext' { PositionedToken TkFunext _ }
  'ua'     { PositionedToken TkUnivalence _ }
  'T'      { PositionedToken (TkTop) _ }
  '_|_'    { PositionedToken (TkBot) _ }
  univ     { PositionedToken (TkUniv $$) _ }
  var      { PositionedToken (TkVar $$) _ }
  int      { PositionedToken (TkInt $$) _ }
  string   { PositionedToken (TkString $$) _ }

%nonassoc ':='
%nonassoc ':' '.' ','
%right '->'
%nonassoc '='
%right 'x'
%right '+'
%nonassoc var univ int '(' '{' '[' '\\' 'T' '_|_' 'U' 'Nat' '*' 'ind' 'succ' 'funext' 'ua'
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

Signature :: { SourceAssumption }
  : var ':' Term { ($1, $3) }

Pragma :: { Pragma }
  : 'check' Term     { Check $2 }
  | 'type' Term      { Type $2 }
  | 'eval' Term      { Eval $2 }
  | 'include' string { Include $ unpack $2 }

Term :: { SourceTerm }
  : '(' Term ')' { $2 }
  | var          { SVar $1 }
  | Terminal     { $1 }
  | univ         { SUniv $1 }
  | Abstraction  { $1 }
  | Application  { $1 }
  | PiType       { $1 }
  | Identity     { $1 }
  | SigmaType    { $1 }
  | CoProduct    { $1 }
  | Tuple        { $1 }
  | NatNums      { $1 }
  | Induction    { $1 }
  | Funext       { $1 }
  | Univalence   { $1 }
  | '*'          { SStar }

Application :: { SourceTerm }
  : Term Term         %prec APP { SApp $1 ($2, Exp) }
  | Term '{' Term '}' %prec APP { SApp $1 ($3, Imp) }

Abstraction :: { SourceTerm }
  : '\\' '(' var ':' Term ')' '.' Term { SLam ($3, Just $5, Exp) $8 }
  | '\\' '{' var ':' Term '}' '.' Term { SLam ($3, Just $5, Imp) $8 }
  | '\\' var '.' Term                  { SLam ($2, Nothing, Exp) $4 }
  | '\\' '{' var '}' '.' Term          { SLam ($3, Nothing, Imp) $6 }

PiType :: { SourceTerm }
  : '(' var ':' Term ')' '->' Term { SPi (Just $2, $4, Exp) $7 }
  | '{' var ':' Term '}' '->' Term { SPi (Just $2, $4, Imp) $7 }
  | Term '->' Term                 { SPi (Nothing, $1, Exp) $3 }

Terminal :: { SourceTerm }
  : 'T'          { STop }
  | '_|_'        { SBot }

Identity :: { SourceTerm }
  : Term '=' Term              { SId Nothing $1 $3 }
  | '=' '[' Term ']'           { SIdFam $3 }
  | Term '=' '[' Term ']' Term { SId (Just $4) $1 $6 }
  | 'refl' '[' Term ']'        { SRefl $3 }

SigmaType :: { SourceTerm }
  : '(' var ':' Term ')' 'x' Term { SSigma (Just $2, $4) $7 }
  | Term 'x' Term                 { SSigma (Nothing, $1) $3 }

CoProduct :: { SourceTerm }
  : Term '+' Term      { SSum $1 $3 }
  | 'inl' '(' Term ')' { SInl $3 }
  | 'inr' '(' Term ')' { SInr $3 }

Terms :: { [SourceTerm] }
  : Term           { [$1] }
  | Term ',' Terms { $1 : $3 }

Tuple :: { SourceTerm }
  : '(' Term ',' Terms ')'
  {
    case $4 of
      []     -> outputParseError $5
      (m:ms) -> parseTuple $2 m ms
  }

NatNums :: { SourceTerm }
  : 'Nat'               { SNat }
  | 'succ' '(' Term ')' { SSucc $3 }
  | int                 { parseNum $1 }

Funext :: { SourceTerm }
  : 'funext' '(' Term ')' { SFunext $3 }

Univalence :: { SourceTerm }
  : 'ua' '(' Term ')' { SUnivalence $3 }

BoundTerm :: { SourceBoundTerm }
  : Term              { SNoBind $1 }
  | var '.' BoundTerm { SBind $1 $3 }

BoundTerms :: { [SourceBoundTerm] }
  :                          { [] }
  | BoundTerm                { [$1] }
  | BoundTerm ',' BoundTerms { $1 : $3 }

BoundTermsList :: { [SourceBoundTerm] }
  :                { [] }
  | ',' BoundTerms { $2 }

Induction :: { SourceTerm }
  : 'ind' '[' Term ']' '(' BoundTerm BoundTermsList ')' 
  {
    case $7 of
      []          -> outputParseError $8
      [SNoBind a] -> SInd $3 $6 [] a
      (_:xs)      -> case last xs of
        SBind _ _ -> outputParseError $8
        SNoBind a -> SInd $3 $6 (init $7) a 
      _           -> outputParseError $8
  }

{
data Pragma
  = Check SourceTerm
  | Type SourceTerm
  | Eval SourceTerm
  | Include FilePath

data Declaration
  = Def SourceAlias
  | Signature SourceAssumption
  | Pragma Pragma

type Program = [Declaration]

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

parseNum :: Integer -> SourceTerm
parseNum 0 = SZero
parseNum n = SSucc $ parseNum (n - 1)

parseTuple :: SourceTerm -> SourceTerm -> [SourceTerm] -> SourceTerm
parseTuple m n []     = SPair m n
parseTuple m n (t:ts) = SPair m $ parseTuple n t ts
}
