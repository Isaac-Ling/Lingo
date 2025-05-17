module Core.Judgement.Utils where

import Core.Term
import Core.Error

import Data.ByteString.Lazy.Char8 (ByteString, pack, unpack)

type TypeCheck a = ReaderT (Environment, Context) (CanErrorT Term) a

