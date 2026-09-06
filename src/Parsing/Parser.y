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
%expect 0

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
  'ind'    { PositionedToken TkInd _ }
  'check'  { PositionedToken TkCheck _ }
  'type'   { PositionedToken TkType _ }
  'eval'   { PositionedToken TkEval _ }
  'include'{ PositionedToken TkInclude _ }
  'inl'    { PositionedToken TkInl _ }
  'inr'    { PositionedToken TkInr _ }
  'refl'   { PositionedToken TkRefl _ }
  'Nat'    { PositionedToken TkNat _ }
  'succ'   { PositionedToken TkSucc _ }
  'T'      { PositionedToken (TkTop) _ }
  '_|_'    { PositionedToken (TkBot) _ }
  '0'      { PositionedToken (TkInt 0) _ }
  univ     { PositionedToken (TkUniv $$) _ }
  var      { PositionedToken (TkVar $$) _ }
  int      { PositionedToken (TkInt $$) _ }
  string   { PositionedToken (TkString $$) _ }

%nonassoc ':='
%nonassoc ':' '.' ','
%right '->'
%nonassoc '='
%nonassoc REDUCE_SUM
%nonassoc var
%right 'x'
%right '+'

%%

Program :: { Program }
  : Declarations { $1 }

Declarations :: { Program }
  :                         { [] }
  | '\n' Declarations       { $2 }
  | Definition Declarations { $1 : $2 }
  | Signature Declarations  { Signature $1 : $2 }
  | Pragma Declarations     { Pragma $1 : $2 }

Definition :: { Declaration }
  : var Params ':=' Term
  {
    Def ($1, SParamTerm (reverse $2) $4)
  }

Param :: { Parameter }
  : var                  { BinderParam ($1, Nothing, Exp) }
  | '(' var ')'          { BinderParam ($2, Nothing, Exp) }
  | '{' var '}'          { BinderParam ($2, Nothing, Imp) }
  | '(' var ':' Term ')' { BinderParam ($2, Just $4, Exp) }
  | '{' var ':' Term '}' { BinderParam ($2, Just $4, Imp) }

  -- TODO: Complete possible constructor patterns
  | '0'                 { Pattern $ SZero }
  | 'succ' '(' var ')'  { Pattern $ SSucc (SVar $3) }
  | '*'                 { Pattern $ SStar }
  | '(' var ',' var ')' { Pattern $ SPair (SVar $2) (SVar $4) }
  | 'inl' '(' var ')'   { Pattern $ SInl $ SVar $3 }
  | 'inr' '(' var ')'   { Pattern $ SInr $ SVar $3 }

Params :: { [Parameter] }
  :              { [] }
  | Param Params { $1 : $2 }

Signature :: { SourceAssumption }
  : var ':' Term { ($1, $3) }

Pragma :: { Pragma }
  : 'check' Term     { Check $2 }
  | 'type' Term      { Type $2 }
  | 'eval' Term      { Eval $2 }
  | 'include' string { Include $ unpack $2 }

Term :: { SourceTerm }
  : Abstraction { $1 }                       
  | PiExpr      { $1 }

Abstraction :: { SourceTerm }
  : '\\' '(' var ':' Term ')' '.' Term { SLam ($3, Just $5, Exp) $8 }
  | '\\' '{' var ':' Term '}' '.' Term { SLam ($3, Just $5, Imp) $8 }
  | '\\' var '.' Term                  { SLam ($2, Nothing, Exp) $4 }
  | '\\' '{' var '}' '.' Term          { SLam ($3, Nothing, Imp) $6 }

PiExpr :: { SourceTerm }
  : '(' Terms ':' Term ')' '->' Term { varListToPis (termsToVars $5 $2) $4 Exp $7 }
  | '{' Terms ':' Term '}' '->' Term { varListToPis (termsToVars $5 $2) $4 Imp $7 }
  | EqExpr '->' Term               { SPi (Nothing, $1, Exp) $3 }
  | EqExpr                         { $1 }

EqExpr :: { SourceTerm }
  : SigmaExpr '=' SigmaExpr              { SId Nothing $1 $3 }
  | SigmaExpr '=' '[' Term ']' SigmaExpr { SId (Just $4) $1 $6 }
  | SigmaExpr                            { $1 }

SigmaExpr :: { SourceTerm }
  : '(' Terms ':' Term ')' 'x' SigmaExpr { varListToSigmas (termsToVars $5 $2) $4 Exp $7 }
  | SumExpr 'x' SigmaExpr              { SSigma (Nothing, $1) $3 }
  | SumExpr                            { $1 }

SumExpr :: { SourceTerm }
  : AppExpr '+' SumExpr      { SSum $1 $3 }
  | AppExpr %prec REDUCE_SUM { $1 } 

AppExpr :: { SourceTerm }
  : AppExpr AtomicTerm   { SApp $1 ($2, Exp) }
  | AppExpr '{' Term '}' { SApp $1 ($3, Imp) }
  | AtomicTerm           { $1 }

AtomicTerm :: { SourceTerm }
  : '(' Terms ')'
    {
      case $2 of
        [t]          -> t
        (m : n : ts) -> parseTuple m n ts
        []           -> outputParseError $3
    }
  | var                    { SVar $1 }
  | univ                   { SUniv $1 }
  | int                    { parseNum $1 }
  | '0'                    { SZero }
  | '*'                    { SStar }
  | 'T'                    { STop }
  | '_|_'                  { SBot }
  | 'Nat'                  { SNat }
  | 'succ' '(' Term ')'    { SSucc $3 }
  | 'inl' '(' Term ')'     { SInl $3 }
  | 'inr' '(' Term ')'     { SInr $3 }
  | 'refl' '[' Term ']'    { SRefl $ Just $3 }
  | 'refl'                 { SRefl Nothing }
  | '=' '[' Term ']'       { SIdFam $3 }
  | 'ind' '[' Term ']' '(' BoundTerm BoundTermsList ')'
    {
      case $7 of
        []          -> outputParseError $8
        [SNoBind a] -> SInd $3 $6 [] a
        (_:xs)      -> case last xs of
          SBind _ _ -> outputParseError $8
          SNoBind a -> SInd $3 $6 (init $7) a
        _           -> outputParseError $8
    }

Terms :: { [SourceTerm] }
  : Term           { [$1] }
  | Term ',' Terms { $1 : $3 }

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

parse :: FilePath -> ByteString -> CanError Program
parse f s = case runAlex s parser of
  Right t -> Result t
  Left er -> case er of
    ""     -> Error SyntaxError Nothing
    (x:xs) -> Error SyntaxError (Just (toUpper x : xs ++ " in source file " ++ show f))

parseNum :: Int -> SourceTerm
parseNum 0 = SZero
parseNum n = SSucc $ parseNum (n - 1)

parseTuple :: SourceTerm -> SourceTerm -> [SourceTerm] -> SourceTerm
parseTuple m n []     = SPair m n
parseTuple m n (t:ts) = SPair m $ parseTuple n t ts

varListToPis :: [ByteString] -> SourceTerm -> Explicitness -> SourceTerm -> SourceTerm
varListToPis []       t e m = m
varListToPis (x:xs)   t e m = SPi (Just x, t, e) $ varListToPis xs t e m

varListToSigmas :: [ByteString] -> SourceTerm -> Explicitness -> SourceTerm -> SourceTerm
varListToSigmas []     t e m = m
varListToSigmas (x:xs) t e m = SSigma (Just x, t) $ varListToSigmas xs t e m

termsToVars :: PositionedToken -> [SourceTerm] -> [ByteString]
termsToVars _ []          = []
termsToVars t (SVar x:ts) = x : termsToVars t ts
termsToVars t _           = outputParseError t
}
