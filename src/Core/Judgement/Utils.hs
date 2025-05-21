module Core.Judgement.Utils where

import Core.Term
import Core.Error

import Data.List (elemIndex)
import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString, pack, unpack)

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
    -- TODO: Don't use "BLAH"...
    go :: Binders -> NamedTerm -> Term
    go bs (NVar x)          = case elemIndex (Just x) bs of
      Just i  -> Var (Bound i)
      Nothing -> Var (Free x)
    go bs (NLam (NImp x) m)      = Lam (Imp x) (go (Just x : bs) m)
    go bs (NLam (NExp (x, t)) m) = Lam (Exp (x, go bs t)) (go (Just x : bs) m)
    go bs (NPi (x, t) m)         = Pi (x, go bs t) (go (Just x : bs) m)
    go bs (NArr t m)             = Pi (pack "BLAH", go bs t) (go (Nothing : bs) m)
    go bs (NSigma (x, t) m)      = Sigma (x, go bs t) (go (Just x : bs) m)
    go bs (NProd t m)            = Sigma (pack "BLAH", go bs t) (go (Nothing : bs) m)
    go bs (NApp m n)             = App (go bs m) (go bs n)
    go bs (NPair m n)            = Pair (go bs m) (go bs n)
    go bs (NInd t m c a)         = Ind (go bs t) (boundTermToDeBruijn bs m) (map (boundTermToDeBruijn bs) c) (go bs a)
    go bs (NUniv i)              = Univ i
    go bs NZero                  = Zero
    go bs NOne                   = One
    go bs NStar                  = Star

    boundTermToDeBruijn :: Binders -> NamedBoundTerm -> BoundTerm
    boundTermToDeBruijn bs (NNoBind m) = NoBind $ go bs m
    boundTermToDeBruijn bs (NBind x m) = Bind x $ boundTermToDeBruijn (Just x : bs) m

resolve :: Environment -> Term -> Term
resolve env (Var (Free x))       = case lookup x env of
  Just m  -> m
  Nothing -> Var $ Free x
resolve env (Var (Bound i))      = Var $ Bound i
resolve env (Lam (Imp x) m)      = Lam (Imp x) (resolve env m)
resolve env (Lam (Exp (x, t)) m) = Lam (Exp (x, resolve env t)) (resolve env m)
resolve env (Pi (x, t) m)        = Pi (x, resolve env t) (resolve env m)
resolve env (Sigma (x, t) m)     = Sigma (x, resolve env t) (resolve env m)
resolve env (App m n)            = App (resolve env m) (resolve env n)
resolve env (Pair m n)           = Pair (resolve env m) (resolve env n)
resolve env (Univ i)             = Univ i
resolve env Zero                 = Zero
resolve env One                  = One
resolve env Star                 = Star
resolve env (Ind t m c a)        = Ind (resolve env t) (resolveBoundTerm env m) (map (resolveBoundTerm env) c) (resolve env a)
  where
    resolveBoundTerm :: Environment -> BoundTerm -> BoundTerm
    resolveBoundTerm env (NoBind m) = NoBind $ resolve env m
    resolveBoundTerm env (Bind x m) = Bind x $ resolveBoundTerm env m

instance Eq BoundTerm where
  NoBind m == NoBind n = m == n
  Bind _ m == Bind _ n = m == n
  _ == _               = False

instance Eq Var where
  Free x == Free y   = x == y
  Bound i == Bound j = i == j
  _ == _             = False

instance Eq Term where
  Var x == Var y = x == y
  Lam (Imp _) m == Lam (Imp _) n            = m == n
  Lam (Exp (x, t)) m == Lam (Exp (y, t')) n = t == t' && m == n
  App m n == App m' n'                      = m == m' && n == n'
  Star == Star                              = True
  Pair m n == Pair m' n'                    = m == m' && n == n'
  Univ i == Univ j                          = i == j
  Zero == Zero                              = True
  One == One                                = True
  Pi (_, t) m == Pi (_, t') n               = t == t' && m == n
  Sigma (_, t) m == Sigma (_, t') n         = t == t' && m == n
  Ind t m c a == Ind t' m' c' a'            = t == t' && m == m' && c == c' && a == a' 
  _ == _                                    = False

instance Show Term where
  show = go []
    where
      go :: [String] -> Term -> String
      go xs (Var (Free x))               = unpack x
      go xs (Var (Bound i))
        | i < length xs = xs !! i
        | otherwise     = "x"
      go xs Star                         = "*"
      go xs (App (Lam xt m) (Lam yt n))  = "(" ++ go xs (Lam xt m) ++ ") " ++ "(" ++ go xs (Lam yt n) ++ ")"
      go xs (App m (Lam xt n))           = go xs m ++ " (" ++ go xs (Lam xt n) ++ ")"
      go xs (App m (App p n))            = go xs m ++ " (" ++ go xs (App p n) ++ ")"
      go xs (App (Lam xt m) n)           = "(" ++ go xs (Lam xt m) ++ ") " ++ go xs n
      go xs (App (Pi xt m) n)            = "(" ++ go xs (Pi xt m) ++ ") " ++ go xs n
      go xs (App (Sigma xt m) n)         = "(" ++ go xs (Sigma xt m) ++ ") " ++ go xs n
      go xs (App m n)                    = go xs m ++ " " ++ go xs n
      go xs (Pair m n)                   = "(" ++ go xs m ++ ", " ++ go xs n ++ ")"
      go xs (Lam (Exp (x, t)) m)         = "\\(" ++ unpack x ++ " : " ++ go xs t ++ "). " ++ go (unpack x : xs) m
      go xs (Lam (Imp x) m)              = "\\" ++ unpack x ++ ". " ++ go (unpack x : xs) m
      go xs (Univ 0)                     = "U"
      go xs (Univ i)                     = "U" ++ show i
      go xs Zero                         = "0"
      go xs One                          = "1"
      go xs (Pi (x, Pi (y, t) m) n)      = "(" ++ go xs (Pi (x, t) m) ++ ") -> " ++ go (unpack x : xs) n
      go xs (Pi (x, t) m)                = "(" ++ unpack x ++ ", " ++ go xs t ++ ") -> " ++ go (unpack x : xs) m
      go xs (Sigma (x, t) (Sigma yt' m)) = "(" ++ unpack x ++ " : " ++ go xs t ++ ") x (" ++ go (unpack x : xs) (Sigma yt' m) ++ show ")"
      go xs (Sigma (x, t) m)             = "(" ++ unpack x ++ " : " ++ go xs t ++ ") x " ++ showSigmaOperarands (unpack x : xs) m
      go xs (Ind t m c a)                = "ind[" ++ go xs t ++ "](" ++ showBoundTerm xs m ++ (if null c then "" else ", ") ++ showBoundTermsNoParen xs c ++ ", " ++ go xs a ++ ")"

      showBoundTerm :: [String] -> BoundTerm -> String
      showBoundTerm xs (NoBind m) = go xs m
      showBoundTerm xs (Bind x m) = unpack x ++ ". " ++ showBoundTerm (unpack x : xs) m

      showBoundTermsNoParen :: [String] -> [BoundTerm] -> String
      showBoundTermsNoParen xs []     = ""
      showBoundTermsNoParen xs [y]    = showBoundTerm xs y
      showBoundTermsNoParen xs (y:ys) = showBoundTerm xs y ++ ", " ++ showBoundTermsNoParen xs ys

      -- TODO: Generalise this to support arbitrary terms with any precedence
      showSigmaOperarands :: [String] -> Term -> String
      showSigmaOperarands xs (App m n) = "(" ++ go xs (App m n) ++ ")"
      showSigmaOperarands xs (Pi t m)  = "(" ++ go xs (Pi t m) ++ ")"
      showSigmaOperarands xs m         = go xs m

