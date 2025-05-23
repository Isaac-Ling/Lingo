module Core.Judgement.Utils where

import Core.Term
import Core.Error

import Data.List (elemIndex)
import Data.Maybe (fromMaybe)
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
    go bs (NVar x)              = case elemIndex (Just x) bs of
      Just i  -> Var (Bound i)
      Nothing -> Var (Free x)
    go bs (NLam (x, Nothing) m)   = Lam (x, Nothing) (go (Just x : bs) m)
    go bs (NLam (x, Just t) m)    = Lam (x, Just $ go bs t) (go (Just x : bs) m)
    go bs (NPi (Just x, t) m)     = Pi (Just x, go bs t) (go (Just x : bs) m)
    go bs (NPi (Nothing, t) m)    = Pi (Nothing, go bs t) (go (Nothing : bs) m)
    go bs (NSigma (Just x, t) m)  = Sigma (Just x, go bs t) (go (Just x : bs) m)
    go bs (NSigma (Nothing, t) m) = Sigma (Nothing, go bs t) (go (Nothing : bs) m)
    go bs (NApp m n)              = App (go bs m) (go bs n)
    go bs (NPair m n)             = Pair (go bs m) (go bs n)
    go bs (NInd t m c a)          = Ind (go bs t) (boundTermToDeBruijn bs m) (map (boundTermToDeBruijn bs) c) (go bs a)
    go bs (NUniv i)               = Univ i
    go bs NZero                   = Zero
    go bs NOne                    = One
    go bs NStar                   = Star

    boundTermToDeBruijn :: Binders -> NamedBoundTerm -> BoundTerm
    boundTermToDeBruijn bs (NNoBind m) = NoBind $ go bs m
    boundTermToDeBruijn bs (NBind x m) = Bind x $ boundTermToDeBruijn (Just x : bs) m

resolve :: Environment -> Term -> Term
resolve env (Var (Free x))       = case lookup x env of
  Just m  -> m
  Nothing -> Var $ Free x
resolve env (Var (Bound i))      = Var $ Bound i
resolve env (Lam (x, Nothing) m) = Lam (x, Nothing) (resolve env m)
resolve env (Lam (x, Just t) m)  = Lam (x, Just $ resolve env t) (resolve env m)
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
  Var x == Var y                           = x == y
  Lam (_, Nothing) m == Lam (_, Nothing) n = m == n
  Lam (_, Just t) m == Lam (_, Just t') n  = t == t' && m == n
  App m n == App m' n'                     = m == m' && n == n'
  Star == Star                             = True
  Pair m n == Pair m' n'                   = m == m' && n == n'
  Univ i == Univ j                         = i == j
  Zero == Zero                             = True
  One == One                               = True
  Pi (_, t) m == Pi (_, t') n              = t == t' && m == n
  Sigma (_, t) m == Sigma (_, t') n        = t == t' && m == n
  Ind t m c a == Ind t' m' c' a'           = t == t' && m == m' && c == c' && a == a' 
  _ == _                                   = False

instance Show Term where
  show = go []
    where
      -- TODO: Ensure names all work
      go :: Binders -> Term -> String
      go bs (Var (Free x))               = unpack x
      go bs (Var (Bound i))
        | i < length bs = unpack $ fromMaybe (pack "a") (bs !! i)
        | otherwise     = "x"
      go bs Star                        = "*"
      go bs (App (Lam xt m) (Lam yt n)) = "(" ++ go bs (Lam xt m) ++ ") " ++ "(" ++ go bs (Lam yt n) ++ ")"
      go bs (App m (Lam xt n))          = go bs m ++ " (" ++ go bs (Lam xt n) ++ ")"
      go bs (App m (App p n))           = go bs m ++ " (" ++ go bs (App p n) ++ ")"
      go bs (App (Lam xt m) n)          = "(" ++ go bs (Lam xt m) ++ ") " ++ go bs n
      go bs (App (Pi xt m) n)           = "(" ++ go bs (Pi xt m) ++ ") " ++ go bs n
      go bs (App (Sigma xt m) n)        = "(" ++ go bs (Sigma xt m) ++ ") " ++ go bs n
      go bs (App m n)                   = go bs m ++ " " ++ go bs n
      go bs (Pair m n)                  = "(" ++ go bs m ++ ", " ++ go bs n ++ ")"
      go bs (Lam (x, Just t) m)         = "\\(" ++ unpack x ++ " : " ++ go bs t ++ "). " ++ go (Just x : bs) m
      go bs (Lam (x, Nothing) m)        = "\\" ++ unpack x ++ ". " ++ go (Just x : bs) m
      go bs (Univ 0)                    = "U"
      go bs (Univ i)                    = "U" ++ show i
      go bs Zero                        = "0"
      go bs One                         = "1"
      go bs (Pi (Nothing, Pi (y, t) m) n) = "(" ++ go bs (Pi (y, t) m) ++ ") -> " ++ go bs n
      go bs (Pi (Just x, t) m)          = "(" ++ unpack x ++ " : " ++ go bs t ++ ") -> " ++ go (Just x : bs) m
      go bs (Pi (Nothing, t) m)         = go bs t ++ " -> " ++ go (Nothing : bs) m
      go bs (Sigma (Just x, t) m)       = "(" ++ unpack x ++ " : " ++ go bs t ++ ") x " ++ showSigmaOperarands (Just x : bs) m
      go bs (Sigma (Nothing, t) m)      = go bs t ++ " x " ++ showSigmaOperarands (Nothing : bs) m
      go bs (Ind t m c a)               = "ind[" ++ go bs t ++ "](" ++ showBoundTerm bs m ++ (if null c then "" else ", ") ++ showBoundTermsNoParen bs c ++ ", " ++ go bs a ++ ")"

      showBoundTerm :: Binders -> BoundTerm -> String
      showBoundTerm bs (NoBind m) = go bs m
      showBoundTerm bs (Bind x m) = unpack x ++ ". " ++ showBoundTerm (Just x : bs) m

      showBoundTermsNoParen :: Binders -> [BoundTerm] -> String
      showBoundTermsNoParen bs []     = ""
      showBoundTermsNoParen bs [y]    = showBoundTerm bs y
      showBoundTermsNoParen bs (y:ys) = showBoundTerm bs y ++ ", " ++ showBoundTermsNoParen bs ys

      -- TODO: Generalise this to support arbitrary terms with any precedence
      showSigmaOperarands :: Binders -> Term -> String
      showSigmaOperarands bs (App m n)   = "(" ++ go bs (App m n) ++ ")"
      showSigmaOperarands bs (Pi t m)    = "(" ++ go bs (Pi t m) ++ ")"
      showSigmaOperarands bs (Sigma t m) = "(" ++ go bs (Sigma t m) ++ ")"
      showSigmaOperarands bs m           = go bs m
