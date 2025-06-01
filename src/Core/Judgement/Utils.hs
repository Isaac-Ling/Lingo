module Core.Judgement.Utils where

import Core.Term
import Core.Error

import Data.List (elemIndex)
import Data.Maybe (fromMaybe)
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
    go bs (NSum m n)            = Sum (go bs m) (go bs n)
    go bs (NId m n)             = Id (go bs m) (go bs n)
    go bs (NInd t m c a)        = Ind (go bs t) (boundTermToDeBruijn bs m) (map (boundTermToDeBruijn bs) c) (go bs a)
    go bs (NUniv i)             = Univ i
    go bs NZero                 = Zero
    go bs NOne                  = One
    go bs (NInl m)              = Inl $ go bs m
    go bs (NInr m)              = Inr $ go bs m
    go bs (NRefl m)             = Refl $ go bs m
    go bs NStar                 = Star

    boundTermToDeBruijn :: Binders -> NamedBoundTerm -> BoundTerm
    boundTermToDeBruijn bs (NNoBind m) = NoBind $ go bs m
    boundTermToDeBruijn bs (NBind x m) = Bind (Just x) $ boundTermToDeBruijn (Just x : bs) m

elaborate :: Environment -> Term -> Term
elaborate env (Var (Free x))       = case lookup x env of
  Just m  -> elaborate env m
  Nothing -> Var $ Free x
elaborate env (Var (Bound i))      = Var $ Bound i
elaborate env (Lam (x, Nothing) m) = Lam (x, Nothing) (elaborate env m)
elaborate env (Lam (x, Just t) m)  = Lam (x, Just $ elaborate env t) (elaborate env m)
elaborate env (Pi (x, t) m)        = Pi (x, elaborate env t) (elaborate env m)
elaborate env (Sigma (x, t) m)     = Sigma (x, elaborate env t) (elaborate env m)
elaborate env (App m n)            = App (elaborate env m) (elaborate env n)
elaborate env (Pair m n)           = Pair (elaborate env m) (elaborate env n)
elaborate env (Sum m n)            = Sum (elaborate env m) (elaborate env n)
elaborate env (Inl m)              = Inl (elaborate env m)
elaborate env (Inr m)              = Inr (elaborate env m)
elaborate env (Refl m)             = Refl (elaborate env m)
elaborate env (Id m n)             = Id (elaborate env m) (elaborate env n)
elaborate env (Ind t m c a)        = Ind (elaborate env t) (elaborateBoundTerm env m) (map (elaborateBoundTerm env) c) (elaborate env a)
  where
    elaborateBoundTerm :: Environment -> BoundTerm -> BoundTerm
    elaborateBoundTerm env (NoBind m) = NoBind $ elaborate env m
    elaborateBoundTerm env (Bind x m) = Bind x $ elaborateBoundTerm env m
elaborate env m                    = m

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
    go k l (Sum m n)            = Sum (go k l m) (go k l n)
    go k l (Id m n)             = Id (go k l m) (go k l n)
    go k l (Inl m)              = Inl $ go k l m
    go k l (Inr m)              = Inr $ go k l m
    go k l (Refl m)             = Refl $ go k l m
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
open m = openFor m 0

openFor :: Term -> Int -> Term -> Term
openFor m k (Var (Bound i))
  | i == k    = m
  | otherwise = Var $ Bound i
openFor m k (Lam (x, Just t) n)  = Lam (x, Just $ openFor m k t) (openFor (bumpUp m) (k + 1) n)
openFor m k (Lam (x, Nothing) n) = Lam (x, Nothing) (openFor (bumpUp m) (k + 1) n)
openFor m k (Pi (x, t) n)        = Pi (x, openFor m k t) (openFor (bumpUp m) (k + 1) n)
openFor m k (Sigma (x, t) n)     = Sigma (x, openFor m k t) (openFor (bumpUp m) (k + 1) n)
openFor m k (Pair t n)           = Pair (openFor m k t) (openFor m k n)
openFor m k (Id t n)             = Id (openFor m k t) (openFor m k n)
openFor m k (Sum t n)            = Sum (openFor m k t) (openFor m k n)
openFor m k (App t n)            = App (openFor m k t) (openFor m k n)
openFor m k (Inl n)              = Inl (openFor m k n)
openFor m k (Inr n)              = Inr (openFor m k n)
openFor m k (Refl n)             = Refl (openFor m k n)
openFor m k (Ind t m' c a)       = Ind (openFor m k t) (openInBoundTerm m k m') (map (openInBoundTerm m k) c) (openFor m k a)
  where
    openInBoundTerm :: Term -> Int -> BoundTerm -> BoundTerm
    openInBoundTerm m k (NoBind n) = NoBind (openFor m k n)
    openInBoundTerm m k (Bind x n) = Bind x (openInBoundTerm (bumpUp m) (k + 1) n)
openFor m k n                    = n

showTermWithBinders :: Binders -> Term -> String
showTermWithBinders bs (Var (Free x))                = unpack x
showTermWithBinders bs (Var (Bound i))
  | i >= 0    = unpack $ fromMaybe (pack errorString) (bs !! i)
  | otherwise = errorString
  where
    errorString :: String
    errorString = "ERROR"
showTermWithBinders bs Star                          = "*"
showTermWithBinders bs (App (Lam xt m) (Lam yt n))   = "(" ++ showTermWithBinders bs (Lam xt m) ++ ") " ++ "(" ++ showTermWithBinders bs (Lam yt n) ++ ")"
showTermWithBinders bs (App m (Lam xt n))            = showTermWithBinders bs m ++ " (" ++ showTermWithBinders bs (Lam xt n) ++ ")"
showTermWithBinders bs (App m (App p n))             = showTermWithBinders bs m ++ " (" ++ showTermWithBinders bs (App p n) ++ ")"
showTermWithBinders bs (App m (Sigma xt n))          = showTermWithBinders bs m ++ " (" ++ showTermWithBinders bs (Sigma xt n) ++ ")"
showTermWithBinders bs (App (Lam xt m) n)            = "(" ++ showTermWithBinders bs (Lam xt m) ++ ") " ++ showTermWithBinders bs n
showTermWithBinders bs (App (Pi xt m) n)             = "(" ++ showTermWithBinders bs (Pi xt m) ++ ") " ++ showTermWithBinders bs n
showTermWithBinders bs (App (Sigma xt m) n)          = "(" ++ showTermWithBinders bs (Sigma xt m) ++ ") " ++ showTermWithBinders bs n
showTermWithBinders bs (App m n)                     = showTermWithBinders bs m ++ " " ++ showTermWithBinders bs n
showTermWithBinders bs (Pair m n)                    = "(" ++ showTermWithBinders bs m ++ ", " ++ showTermWithBinders bs n ++ ")"
showTermWithBinders bs (Id m n)                      = showTermWithBinders bs m ++ " = " ++ showTermWithBinders bs n
showTermWithBinders bs (Sum m n)                     = showTermWithBinders bs m ++ " + " ++ showTermWithBinders bs n
showTermWithBinders bs (Lam (x, Just t) m)           = "\\(" ++ unpack x ++ " : " ++ showTermWithBinders bs t ++ "). " ++ showTermWithBinders (Just x : bs) m
showTermWithBinders bs (Lam (x, Nothing) m)          = "\\" ++ unpack x ++ ". " ++ showTermWithBinders (Just x : bs) m
showTermWithBinders bs (Univ 0)                      = "U"
showTermWithBinders bs (Univ i)                      = "U" ++ show i
showTermWithBinders bs Zero                          = "0"
showTermWithBinders bs One                           = "1"
showTermWithBinders bs (Inl m)                       = "inl(" ++ showTermWithBinders bs m ++ ")"
showTermWithBinders bs (Inr m)                       = "inr(" ++ showTermWithBinders bs m ++ ")"
showTermWithBinders bs (Refl m)                      = "refl[" ++ showTermWithBinders bs m ++ "]"
showTermWithBinders bs (Pi (Nothing, Pi (y, t) m) n) = "(" ++ showTermWithBinders bs (Pi (y, t) m) ++ ") -> " ++ showTermWithBinders (Nothing : bs) n
showTermWithBinders bs (Pi (Just x, t) m)            = "(" ++ unpack x ++ " : " ++ showTermWithBinders bs t ++ ") -> " ++ showTermWithBinders (Just x : bs) m
showTermWithBinders bs (Pi (Nothing, t) m)           = showTermWithBinders bs t ++ " -> " ++ showTermWithBinders (Nothing : bs) m
showTermWithBinders bs (Sigma (Just x, t) m)         = "(" ++ unpack x ++ " : " ++ showTermWithBinders bs t ++ ") x " ++ showSigmaOperarands (Just x : bs) m
showTermWithBinders bs (Sigma (Nothing, t) m)        = showSigmaOperarands bs t ++ " x " ++ showSigmaOperarands (Nothing : bs) m
showTermWithBinders bs (Ind t m c a)                 = "ind[" ++ showTermWithBinders bs t ++ "](" ++ showBoundTerm bs m ++ (if null c then "" else ", ") ++ showBoundTermsNoParen bs c ++ ", " ++ showTermWithBinders bs a ++ ")"
  where
    showBoundTerm :: Binders -> BoundTerm -> String
    showBoundTerm bs (NoBind m)        = showTermWithBinders bs m
    showBoundTerm bs (Bind (Just x) m) = unpack x ++ ". " ++ showBoundTerm (Just x : bs) m
    showBoundTerm bs (Bind Nothing m)  = showBoundTerm (Nothing : bs) m

    showBoundTermsNoParen :: Binders -> [BoundTerm] -> String
    showBoundTermsNoParen bs []     = ""
    showBoundTermsNoParen bs [y]    = showBoundTerm bs y
    showBoundTermsNoParen bs (y:ys) = showBoundTerm bs y ++ ", " ++ showBoundTermsNoParen bs ys

-- TODO: Generalise this to support arbitrary terms with any precedence
showSigmaOperarands :: Binders -> Term -> String
showSigmaOperarands bs (App m n)   = "(" ++ showTermWithBinders bs (App m n) ++ ")"
showSigmaOperarands bs (Pi t m)    = "(" ++ showTermWithBinders bs (Pi t m) ++ ")"
showSigmaOperarands bs (Sigma t m) = "(" ++ showTermWithBinders bs (Sigma t m) ++ ")"
showSigmaOperarands bs (Sum m n)   = "(" ++ showTermWithBinders bs (Sum m n) ++ ")"
showSigmaOperarands bs m           = showTermWithBinders bs m

instance Show Term where
  show = showTermWithBinders binders
    where
      -- TODO: Ensure these are fresh
      binders :: [Maybe ByteString]
      binders = [Just $ pack ("a" ++ show i) | i <- [0..]]
