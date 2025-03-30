{
module Lexing.Lexer where

import Lexing.Tokens
}

%wrapper "basic"

$digit = [ 0-9 ]
$lower = [ a-z ]
$upper = [ A-Z ]

@id = ($lower | $upper | "_") ($lower | $upper | "_" | "\'")*

tokens :-

$white+  ;
"\\"     { \s -> Backslash }
"."      { \s -> Dot }
"("      { \s -> LParen }
")"      { \s -> RParen }
@id      { \s -> Id s }
