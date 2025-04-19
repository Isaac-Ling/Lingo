{
module Lexing.Lexer where

import Lexing.Tokens

import Data.ByteString.Lazy.Char8 (ByteString, unpack)
}

%encoding "latin1"
%wrapper "basic-bytestring"

$digit = [ 0-9 ]
$lower = [ a-z ]
$upper = [ A-Z ]

@id  = ($lower | $upper | \_) ($lower | $upper | \_ | \')*
@int = $digit+

tokens :-

$white+ ;
<0> \\      { \s -> TkBackslash }
<0> \.      { \s -> TkDot }
<0> \(      { \s -> TkLParen }
<0> \)      { \s -> TkRParen }
<0> ":="    { \s -> TkColonEqual }
<0> \:      { \s -> TkColon }
<0> "->"    { \s -> TkRArrow }
<0> \*      { \s -> TkStar }
<0> \U      { \s -> TkU }
<0> @id     { \s -> TkID s }
<0> @int    { \s -> TkInt $ read $ unpack s }
