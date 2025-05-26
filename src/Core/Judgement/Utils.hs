module Core.Judgement.Utils where

import Core.Term
import Core.Error

import Data.List (elemIndex)
import Data.Maybe (fromMaybe)
import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString, pack, unpack)

-- A list of binders, where the ith element is the ith binder away from the
-- current term. Nothing is used if we should never match against that binder
type Binders = [Maybe ByteString]

toDeBruijn :: NamedTerm -> Term
toDeBruijn = go []
  where
    go :: Binders -> NamedTerm -> Term
    go bs (NVar x)              = case elemIndex (Just x) bs of
      Just i  -> Var (Bound i)
      Nothing -> Var (Free x)
    go bs (NLam (x, Nothing) m) = Lam (x, Nothing) (go (Just x : bs) m)
    go bs (NLam (x, Just t) m)  = Lam (x, Just $ go bs t) (go (Just x : bs) m)
    go bs (NPi (x, t) m)        = Pi (x, go bs t) (go (x : bs) m)
    go bs (NSigma (x, t) m)     = Sigma (x, go bs t) (go (x : bs) m)
    go bs (NApp m n)            = App (go bs m) (go bs n)
    go bs (NPair m n)           = Pair (go bs m) (go bs n)
    go bs (NInd t m c a)        = Ind (go bs t) (boundTermToDeBruijn bs m) (map (boundTermToDeBruijn bs) c) (go bs a)
    go bs (NUniv i)             = Univ i
    go bs NZero                 = Zero
    go bs NOne                  = One
    go bs NStar                 = Star

    boundTermToDeBruijn :: Binders -> NamedBoundTerm -> BoundTerm
    boundTermToDeBruijn bs (NNoBind m) = NoBind $ go bs m
    boundTermToDeBruijn bs (NBind x m) = Bind (Just x) $ boundTermToDeBruijn (Just x : bs) m

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
resolve env (Ind t m c a)        = Ind (resolve env t) (resolveBoundTerm env m) (map (resolveBoundTerm env) c) (resolve env a)
  where
    resolveBoundTerm :: Environment -> BoundTerm -> BoundTerm
    resolveBoundTerm env (NoBind m) = NoBind $ resolve env m
    resolveBoundTerm env (Bind x m) = Bind x $ resolveBoundTerm env m
resolve env m                    = m

shift :: Int -> Term -> Term
shift k = go k 0
  where
    -- Second Int is the minimum index that should be shifted
    -- This is used to only shift 'dangling' indices and not
    -- ones that are bound in the given term
    go :: Int -> Int -> Term -> Term
    go k l (Var (Bound i))
      | i >= l    = Var $ Bound (i + k)
      | otherwise = Var $ Bound i
    go k l (Lam (x, Nothing) m) = Lam (x, Nothing) (go k (l + 1) m)
    go k l (Lam (x, Just t) m)  = Lam (x, Just $ go k l m) (go k (l + 1) m)
    go k l (Pi (x, t) m)        = Pi (x, go k l t) (go k (l + 1)  m)
    go k l (Sigma (x, t) m)     = Sigma (x, go k l t) (go k (l + 1) m)
    go k l (App m n)            = App (go k l m) (go k l n)
    go k l (Pair m n)           = Pair (go k l m) (go k l n)
    go k l (Ind t m c a)        = Ind (go k l t) (shiftInBoundTerm k l m) (map (shiftInBoundTerm k l) c) (go k l a)
    go k l m                    = m

    shiftInBoundTerm :: Int -> Int -> BoundTerm -> BoundTerm
    shiftInBoundTerm k l (NoBind m) = NoBind $ go k l m
    shiftInBoundTerm k l (Bind a m) = Bind a $ shiftInBoundTerm k (l + 1) m

bumpUp :: Term -> Term
bumpUp = shift 1

bumpDown :: Term -> Term
bumpDown = shift (-1)

-- Opening a term with another term refers to substituting the former term for bound variables
-- of index 0 in the latter term
open :: Term -> Term -> Term
open m = go m 0
  where
    go :: Term -> Int -> Term -> Term
    go m k (Var (Bound i))
      | i == k    = m
      | otherwise = Var $ Bound i
    go m k (Lam (x, Just t) n)  = Lam (x, Just $ go m k t) (go (bumpUp m) (k + 1) n)
    go m k (Lam (x, Nothing) n) = Lam (x, Nothing) (go (bumpUp m) (k + 1) n)
    go m k (Pi (x, t) n)        = Pi (x, go m k t) (go (bumpUp m) (k + 1) n)
    go m k (Sigma (x, t) n)     = Sigma (x, go m k t) (go (bumpUp m) (k + 1) n)
    go m k (Pair t n)           = Pair (go m k t) (go m k n)
    go m k (App t n)            = App (go m k t) (go m k n)
    go m k (Ind t m' c a)       = Ind (go m k t) (openInBoundTerm m k m') (map (openInBoundTerm m k) c) (go m k a)
    go m k n                    = n

    openInBoundTerm :: Term -> Int -> BoundTerm -> BoundTerm
    openInBoundTerm m k (NoBind n) = NoBind (go m k n)
    openInBoundTerm m k (Bind x n) = Bind x (openInBoundTerm (bumpUp m) (k + 1) n)

instance Show Term where
  show = go binders
    where
      -- TODO: Ensure these are fresh
      binders :: [Maybe ByteString]
      binders = [Just $ pack ("a" ++ show i) | i <- [0..]]

      errorString :: String
      errorString = "ERROR"

      -- TODO: Ensure names all work
      go :: Binders -> Term -> String
      go bs (Var (Free x))               = unpack x
      go bs (Var (Bound i))
        | i >= 0    = unpack $ fromMaybe (pack errorString) (bs !! i)
        | otherwise = errorString
      go bs Star                        = "*"
      go bs (App (Lam xt m) (Lam yt n)) = "(" ++ go bs (Lam xt m) ++ ") " ++ "(" ++ go bs (Lam yt n) ++ ")"
      go bs (App m (Lam xt n))          = go bs m ++ " (" ++ go bs (Lam xt n) ++ ")"
      go bs (App m (App p n))           = go bs m ++ " (" ++ go bs (App p n) ++ ")"
      go bs (App m (Sigma xt n))        = go bs m ++ " (" ++ go bs (Sigma xt n) ++ ")"
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
      go bs (Pi (Nothing, Pi (y, t) m) n) = "(" ++ go bs (Pi (y, t) m) ++ ") -> " ++ go (Nothing : bs) n
      go bs (Pi (Just x, t) m)          = "(" ++ unpack x ++ " : " ++ go bs t ++ ") -> " ++ go (Just x : bs) m
      go bs (Pi (Nothing, t) m)         = go bs t ++ " -> " ++ go (Nothing : bs) m
      go bs (Sigma (Just x, t) m)       = "(" ++ unpack x ++ " : " ++ go bs t ++ ") x " ++ showSigmaOperarands (Just x : bs) m
      go bs (Sigma (Nothing, t) m)      = go bs t ++ " x " ++ showSigmaOperarands (Nothing : bs) m
      go bs (Ind t m c a)               = "ind[" ++ go bs t ++ "](" ++ showBoundTerm bs m ++ (if null c then "" else ", ") ++ showBoundTermsNoParen bs c ++ ", " ++ go bs a ++ ")"

      showBoundTerm :: Binders -> BoundTerm -> String
      showBoundTerm bs (NoBind m)        = go bs m
      showBoundTerm bs (Bind (Just x) m) = unpack x ++ ". " ++ showBoundTerm (Just x : bs) m
      showBoundTerm bs (Bind Nothing m)  = showBoundTerm (Nothing : bs) m

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
