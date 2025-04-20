{
module Lexing.Lexer where

import Lexing.Tokens

import Data.ByteString.Lazy.Char8 (ByteString, unpack)
}

%encoding "latin1"
%wrapper "posn-bytestring"

$digit = [ 0-9 ]
$lower = [ a-z ]
$upper = [ A-Z ]

@id  = ($lower | $upper | \_) ($lower | $upper | \_ | \')*
@int = $digit+

tokens :-

<0> $white+ ;
<0> \\      { \p s -> PositionedToken TkBackslash p }
<0> \.      { \p s -> PositionedToken TkDot p }
<0> \(      { \p s -> PositionedToken TkLParen p }
<0> \)      { \p s -> PositionedToken TkRParen p }
<0> ":="    { \p s -> PositionedToken TkColonEqual p }
<0> \:      { \p s -> PositionedToken TkColon p }
<0> "->"    { \p s -> PositionedToken TkRArrow p }
<0> \*      { \p s -> PositionedToken TkStar p }
<0> \U      { \p s -> PositionedToken (TkUniv 0) p }
<0> @id     { \p s -> PositionedToken (TkID s) p }
<0> @int    { \p s -> PositionedToken (TkInt $ read $ unpack s) p }

{
data PositionedToken = PositionedToken
  { ptToken    :: Token
  , ptPosition :: AlexPosn
  }
}
