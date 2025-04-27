{
module Lexing.Lexer where

import Lexing.Tokens
import Core.Error

import Data.ByteString.Lazy.Char8 (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
}

%encoding "latin1"
%wrapper "monad-bytestring"

$digit = [ 0-9 ]
$lower = [ a-z ]
$upper = [ A-Z ]

@id   = ($lower | $upper | \_)+ (\')*
@int  = $digit+
@univ = \U $digit+

lingo :-

<0> $white+ ;
<0> "--"\-*.* { skip }

<0> \\        { createTk TkBackslash }
<0> \.        { createTk TkDot }
<0> \,        { createTk TkComma }
<0> \x        { createTk TkCross }
<0> \(        { createTk TkLParen }
<0> \)        { createTk TkRParen }
<0> \[        { createTk TkLSqParen }
<0> \]        { createTk TkRSqParen }
<0> ":="      { createTk TkColonEqual }
<0> \:        { createTk TkColon }
<0> "->"      { createTk TkRArrow }
<0> \*        { createTk TkStar }
<0> "ind"     { createTk TkInd }
<0> @univ     { createUnivTk }
<0> \U        { createTk $ TkUniv 0 }
<0> @id       { createIDTk }
<0> @int      { createIntTk }

{
alexEOF :: Alex PositionedToken
alexEOF = do
  ((AlexPn _ line col), _, _, _) <- alexGetInput
  return $ PositionedToken TkEOF (line, col)

createIDTk :: AlexAction PositionedToken
createIDTk (start@(AlexPn _ line col), _, str, _) len =
  return PositionedToken 
    { ptToken = TkID $ BS.take len str
    , ptPosition = (line, col)
    }

createIntTk :: AlexAction PositionedToken
createIntTk ((AlexPn _ line col), _, str, _) len = return PositionedToken 
  { ptToken = TkInt $ read $ BS.unpack $ BS.take len str
  , ptPosition = (line, col)
  }

createUnivTk :: AlexAction PositionedToken
createUnivTk ((AlexPn _ line col), _, str, _) len = return PositionedToken 
  { ptToken = TkUniv $ getUnivLevel $ BS.unpack $ BS.take len str
  , ptPosition = (line, col)
  }
  where
    getUnivLevel :: String -> Integer
    getUnivLevel []     = 0
    getUnivLevel (u:i) = case i of
      []    -> 0
      level -> read level

createTk :: Token -> AlexAction PositionedToken
createTk tk ((AlexPn _ line col), _, _, _) len = return PositionedToken { ptToken = tk, ptPosition = (line, col) }

scan :: ByteString -> Either String [PositionedToken]
scan s = runAlex s $ loop
  where 
  loop = do
    tk <- alexMonadScan
    if ptToken tk == TkEOF
      then return [tk]
      else (tk : ) <$> loop
}
