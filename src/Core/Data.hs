module Core.Data where

import Data.ByteString.Lazy.Char8 (ByteString, unpack)

data Annotation
  = VarAnno ByteString Type
  deriving Eq

data Term
  = Anno Term Type
  | Star
  | Var ByteString
  | App Term Term
  | Lam Annotation Term
  deriving Eq

instance Show Term where
  show (Anno e t)                      = show e ++ " : " ++ show t
  show (Var x)                         = unpack x
  show Star                            = "*"
  show (App e (Lam xt e'))             = show e ++ " (" ++ show (Lam xt e') ++ ")"
  show (App e (Anno e' t))             = show e ++ " (" ++ show (Anno e' t) ++ ")"
  show (App (Lam xt e) e')             = "(" ++ show (Lam xt e) ++ ") " ++ show e'
  show (App (Anno e t) e')             = "(" ++ show (Anno e t) ++ ") " ++ show e'
  show (App e e')                      = show e ++ " " ++ show e'
  show (Lam (VarAnno x t) (Anno e t')) = "\\" ++ unpack x ++ " : " ++ show t ++ ". (" ++ show (Anno e t') ++ ")"
  show (Lam (VarAnno x t) e)           = "\\" ++ unpack x ++ " : " ++ show t ++ ". " ++ show e

data Type
  = Zero
  | One
  | Arr Type Type
  deriving Eq

instance Show Type where
  show Zero              = "0"
  show One               = "1"
  show (Arr (Arr a b) c) = "(" ++ show (Arr a b) ++ ") -> " ++ show c
  show (Arr a b)         = show a ++ " -> " ++ show b
