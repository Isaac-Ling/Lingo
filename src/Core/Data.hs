module Core.Data where

import Data.ByteString.Lazy.Char8 (ByteString, unpack)

data Term
  = Anno Term Type
  | Var ByteString
  | App Term Term
  | Lam ByteString Term
  deriving Eq

instance Show Term where
  show (Anno e t)          = show e ++ " : " ++ show t
  show (Var x)             = unpack x
  show (App e (Lam x e'))  = show e ++ " (" ++ show (Lam x e') ++ ")"
  show (App e (Anno e' t)) = show e ++ " (" ++ show (Anno e' t) ++ ")"
  show (App (Lam x e) e')  = "(" ++ show (Lam x e) ++ ") " ++ show e'
  show (App (Anno e t) e') = "(" ++ show (Anno e t) ++ ") " ++ show e'
  show (App e e')          = show e ++ " " ++ show e'
  show (Lam x (Anno e t))  = "\\" ++ unpack x ++ ". (" ++ show (Anno e t) ++ ")"
  show (Lam x e)           = "\\" ++ unpack x ++ ". " ++ show e

data Type
  = Singl
  | Arr Type Type
  deriving Eq

instance Show Type where
  show Singl              = "()"
  show (Arr (Arr a b) c) = "(" ++ show (Arr a b) ++ ") -> " ++ show c
  show (Arr a b)         = show a ++ " -> " ++ show b
