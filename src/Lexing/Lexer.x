{
module Lexing.Lexer where

import Lexing.Tokens
}

%encoding "latin1"
%wrapper "basic-bytestring"

$digit = [ 0-9 ]
$lower = [ a-z ]
$upper = [ A-Z ]

@id = ($lower | $upper | \_) ($lower | $upper | \_ | \')*

tokens :-

$white+ ;
<0> \\   { \s -> Backslash }
<0> \.   { \s -> Dot }
<0> \(   { \s -> LParen }
<0> \)   { \s -> RParen }
<0> @id  { \s -> Id s }
<0> \:   { \s -> Colon }
<0> "->" { \s -> RArrow }
<0> "->" { \s -> RArrow }
