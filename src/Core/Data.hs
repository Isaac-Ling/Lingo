module Core.Data where

import Data.ByteString.Lazy.Char8 (ByteString, unpack)

data Term
  = Anno Term Type
  | Var ByteString
  | App Term Term
  | Lam ByteString Term
  deriving Eq

instance Show Term where
  show (Anno x t)         = show x ++ " : " ++ show t
  show (Var x)            = unpack x
  show (App x (Lam y z))  = show x ++ " (" ++ show (Lam y z) ++ ")"
  show (App x (Anno y t)) = show x ++ " (" ++ show (Anno y t) ++ ")"
  show (App x y)          = show x ++ " " ++ show y
  show (Lam x (Anno y t)) = "\\" ++ unpack x ++ ". (" ++ show (Anno y t) ++ ")"
  show (Lam x y)          = "\\" ++ unpack x ++ ". " ++ show y

data Type
  = TVar ByteString
  | Arr Type Type
  deriving Eq

instance Show Type where
  show (TVar a)          = unpack a
  show (Arr (Arr a b) c) = "(" ++ show (Arr a b) ++ ") -> " ++ show c
  show (Arr a b)         = show a ++ " -> " ++ show b
