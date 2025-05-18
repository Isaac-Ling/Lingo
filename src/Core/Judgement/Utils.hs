module Core.Judgement.Utils where

import Core.Term
import Core.Error

import Data.List (elemIndex)
import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString, unpack)

-- This context records the type of bound variables, where the ith type in the
-- context is the type of the ith binder away from the current term
type BoundContext = [Term]

type TypeCheck a = ReaderT (BoundContext, Context) CanError a

-- A list of binders, where the ith element is the ith binder away from the
-- current term. Nothing is used if we should never match against that binder
type Binders = [Maybe ByteString]

toDeBruijn :: NamedTerm -> Term
toDeBruijn = go []
  where
    go :: Binders -> NamedTerm -> Term
    go bs (NVar x)          = case elemIndex (Just x) bs of
      Just i  -> Var (Bound i)
      Nothing -> Var (Free x)
    go bs (NLam (NImp x) m)      = Lam Nothing (go (Just x : bs) m)
    go bs (NLam (NExp (x, t)) m) = Lam (Just (go bs t)) (go (Just x : bs) m)
    go bs (NPi (x, t) m)         = Pi (go bs t) (go (Just x : bs) m)
    go bs (NArr t m)             = Pi (go bs t) (go (Nothing : bs) m)
    go bs (NSigma (x, t) m)      = Sigma (go bs t) (go (Just x : bs) m)
    go bs (NProd t m)            = Sigma (go bs t) (go (Nothing : bs) m)
    go bs (NApp m n)             = App (go bs m) (go bs n)
    go bs (NPair m n)            = Pair (go bs m) (go bs n)
    go bs (NInd t m c a)         = Ind (go bs t) (boundTermToDeBruijn bs m) (map (boundTermToDeBruijn bs) c) (go bs a)
    go bs (NUniv i)              = Univ i
    go bs NZero                  = Zero
    go bs NOne                   = One
    go bs NStar                  = Star

    boundTermToDeBruijn :: Binders -> NamedBoundTerm -> BoundTerm
    boundTermToDeBruijn bs (NNoBind m) = NoBind $ go bs m
    boundTermToDeBruijn bs (NBind x m) = Bind $ boundTermToDeBruijn (Just x : bs) m

resolve :: Environment -> Term -> Term
resolve env (Var (Free x))   = case lookup x env of
  Just m  -> m
  Nothing -> Var $ Free x
resolve env (Var (Bound i))  = Var $ Bound i
resolve env (Lam Nothing m)  = Lam Nothing (resolve env m)
resolve env (Lam (Just t) m) = Lam (Just (resolve env t)) (resolve env m)
resolve env (Pi t m)         = Pi (resolve env t) (resolve env m)
resolve env (Sigma t m)      = Sigma (resolve env t) (resolve env m)
resolve env (App m n)        = App (resolve env m) (resolve env n)
resolve env (Pair m n)       = Pair (resolve env m) (resolve env n)
resolve env (Univ i)         = Univ i
resolve env Zero             = Zero
resolve env One              = One
resolve env Star             = Star
resolve env (Ind t m c a)    = Ind (resolve env t) (resolveBoundTerm env m) (map (resolveBoundTerm env) c) (resolve env a)
  where
    resolveBoundTerm :: Environment -> BoundTerm -> BoundTerm
    resolveBoundTerm env (NoBind m) = NoBind $ resolve env m
    resolveBoundTerm env (Bind m)   = Bind $ resolveBoundTerm env m

instance Show Var where
  show (Free x)  = unpack x
  show (Bound i) = show i

instance Show BoundTerm where
  show (NoBind m) = show m
  show (Bind m)   = show m

-- TODO: Pretty print De Bruijn term
instance Show Term where
  show (Var x)                          = show x
  show Star                             = "*"
  show (App (Lam xt m) (Lam yt n))      = "(" ++ show (Lam xt m) ++ ") " ++ "(" ++ show (Lam yt n) ++ ")"
  show (App m (Lam xt n))               = show m ++ " (" ++ show (Lam xt n) ++ ")"
  show (App m (App p n))                = show m ++ " (" ++ show (App p n) ++ ")"
  show (App (Lam xt m) n)               = "(" ++ show (Lam xt m) ++ ") " ++ show n
  show (App (Pi xt m) n)                = "(" ++ show (Pi xt m) ++ ") " ++ show n
  show (App (Sigma xt m) n)             = "(" ++ show (Sigma xt m) ++ ") " ++ show n
  show (App m n)                        = show m ++ " " ++ show n
  show (Pair m n)                       = "(" ++ show m ++ ", " ++ show n ++ ")"
  show (Lam (Just t) m)                 = "\\(" ++ "x" ++ " : " ++ show t ++ "). " ++ show m
  show (Lam Nothing m)                  = "\\" ++ "x" ++ ". " ++ show m
  show (Univ 0)                         = "U"
  show (Univ i)                         = "U" ++ show i
  show Zero                             = "0"
  show One                              = "1"
  show (Pi (Pi t m) n)                  = "(" ++ show (Pi t m) ++ ") -> " ++ show n
  show (Pi t m)                         = show t ++ " -> " ++ show m
  show (Sigma t (Sigma t' m))           = showSigmaOperarands t ++ " x (" ++ show (Sigma t' m) ++ show ")"
  show (Sigma t m)                      = showSigmaOperarands t ++ " x " ++ showSigmaOperarands m
  show (Ind t m e a)                    = "ind[" ++ show t ++ "](" ++ show m ++ (if null e then "" else ", ") ++ showListNoParen e ++ ", " ++ show a ++ ")"

showListNoParen :: Show a => [a] -> String
showListNoParen []     = ""
showListNoParen [x]    = show x
showListNoParen (x:xs) = show x ++ ", " ++ showListNoParen xs

-- TODO: Generalise this to support arbitrary terms with any precedence
showSigmaOperarands :: Term -> String
showSigmaOperarands (App m n) = "(" ++ show (App m n) ++ ")"
showSigmaOperarands (Pi t m)  = "(" ++ show (Pi t m) ++ ")"
showSigmaOperarands m         = show m
