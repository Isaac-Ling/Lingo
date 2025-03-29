{
module Lexing.Lexer where

import Lexing.Support
}

%wrapper "basic"

$digit = [ 0-9 ]
$lower = [ a-z ]
$upper = [ A-Z ]

@id = ($lower | $upper | \_ | \')*

tokens :-

$white+  ;
"\\"     { \s -> Backslash }
"."      { \s -> Dot }
"("      { \s -> LParen }
")"      { \s -> RParen }
@id     { \s -> Id s }
