module Core.Judgement.Utils where

import Core.Term
import Core.Error

import Control.Monad ( join )
import Data.List (elemIndex, (!?))
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
    go bs (NPi (x, t, ex) m)    = Pi (x, go bs t, ex) (go (x : bs) m)
    go bs (NSigma (x, t) m)     = Sigma (x, go bs t) (go (x : bs) m)
    go bs (NApp m n)            = App (go bs m) (go bs n)
    go bs (NPair m n)           = Pair (go bs m) (go bs n)
    go bs (NSum m n)            = Sum (go bs m) (go bs n)
    go bs (NIdFam t)            = IdFam $ go bs t
    go bs (NId t m n)           = Id (fmap (go bs) t) (go bs m) (go bs n)
    go bs (NInd t m c a)        = Ind (go bs t) (boundTermToDeBruijn bs m) (map (boundTermToDeBruijn bs) c) (go bs a)
    go bs (NUniv i)             = Univ i
    go bs NBot                  = Bot
    go bs NTop                  = Top
    go bs NNat                  = Nat
    go bs NZero                 = Zero
    go bs (NSucc m)             = Succ $ go bs m
    go bs (NInl m)              = Inl $ go bs m
    go bs (NInr m)              = Inr $ go bs m
    go bs (NFunext p)           = Funext $ go bs p
    go bs (NUnivalence f)       = Univalence $ go bs f
    go bs (NRefl m)             = Refl $ go bs m
    go bs NStar                 = Star

    boundTermToDeBruijn :: Binders -> NamedBoundTerm -> BoundTerm
    boundTermToDeBruijn bs (NNoBind m) = NoBind $ go bs m
    boundTermToDeBruijn bs (NBind x m) = Bind (Just x) $ boundTermToDeBruijn (Just x : bs) m

elaborate :: Term -> Term -> Term
elaborate m (Pi (Just x, t, Imp) n) = Lam (x, Just t) $ elaborate m n
elaborate m (Pi (Just x, t, Exp) n) = elaborate m n
elaborate m _                       = m

resolve :: Environment -> Term -> Term
resolve env (Var (Free x))       = case lookup x env of
  Just m  -> resolve env m
  Nothing -> Var $ Free x
resolve env (Var (Bound i))      = Var $ Bound i
resolve env (Lam (x, Nothing) m) = Lam (x, Nothing) (resolve env m)
resolve env (Lam (x, Just t) m)  = Lam (x, Just $ resolve env t) (resolve env m)
resolve env (Pi (x, t, ex) m)    = Pi (x, resolve env t, ex) (resolve env m)
resolve env (Sigma (x, t) m)     = Sigma (x, resolve env t) (resolve env m)
resolve env (App m n)            = App (resolve env m) (resolve env n)
resolve env (Pair m n)           = Pair (resolve env m) (resolve env n)
resolve env (Sum m n)            = Sum (resolve env m) (resolve env n)
resolve env (Inl m)              = Inl $ resolve env m
resolve env (Inr m)              = Inr $ resolve env m
resolve env (Refl m)             = Refl $ resolve env m
resolve env (Succ m)             = Succ $ resolve env m
resolve env (IdFam t)            = IdFam $ resolve env t
resolve env (Funext p)           = Funext $ resolve env p
resolve env (Univalence a)       = Univalence $ resolve env a
resolve env (Id mt m n)          = Id (fmap (resolve env) mt) (resolve env m) (resolve env n)
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
    go k l (Pi (x, t, ex) m)    = Pi (x, go k l t, ex) (go k (l + 1) m)
    go k l (Sigma (x, t) m)     = Sigma (x, go k l t) (go k (l + 1) m)
    go k l (App m n)            = App (go k l m) (go k l n)
    go k l (Pair m n)           = Pair (go k l m) (go k l n)
    go k l (Sum m n)            = Sum (go k l m) (go k l n)
    go k l (IdFam t)            = IdFam (go k l t)
    go k l (Id mt m n)          = Id (fmap (go k l) mt) (go k l m) (go k l n)
    go k l (Inl m)              = Inl $ go k l m
    go k l (Inr m)              = Inr $ go k l m
    go k l (Succ m)             = Succ $ go k l m
    go k l (Refl m)             = Refl $ go k l m
    go k l (Funext p)           = Funext $ go k l p
    go k l (Univalence a)       = Funext $ go k l a
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
openFor m k (Pi (x, t, ex) n)    = Pi (x, openFor m k t, ex) (openFor (bumpUp m) (k + 1) n)
openFor m k (Sigma (x, t) n)     = Sigma (x, openFor m k t) (openFor (bumpUp m) (k + 1) n)
openFor m k (Pair t n)           = Pair (openFor m k t) (openFor m k n)
openFor m k (IdFam t)            = IdFam $ openFor m k t
openFor m k (Id mt t n)          = Id (fmap (openFor m k) mt) (openFor m k t) (openFor m k n)
openFor m k (Sum t n)            = Sum (openFor m k t) (openFor m k n)
openFor m k (App t n)            = App (openFor m k t) (openFor m k n)
openFor m k (Inl n)              = Inl $ openFor m k n
openFor m k (Inr n)              = Inr $ openFor m k n
openFor m k (Refl n)             = Refl $ openFor m k n
openFor m k (Succ n)             = Succ $ openFor m k n
openFor m k (Funext p)           = Funext $ openFor m k p
openFor m k (Univalence a)       = Univalence $ openFor m k a
openFor m k (Ind t m' c a)       = Ind (openFor m k t) (openInBoundTerm m k m') (map (openInBoundTerm m k) c) (openFor m k a)
  where
    openInBoundTerm :: Term -> Int -> BoundTerm -> BoundTerm
    openInBoundTerm m k (NoBind n) = NoBind (openFor m k n)
    openInBoundTerm m k (Bind x n) = Bind x (openInBoundTerm (bumpUp m) (k + 1) n)
openFor m k n                    = n

showTermWithBinders :: Binders -> Term -> String
showTermWithBinders bs (Var (Free x))                = unpack x
showTermWithBinders bs (Var (Bound i))
  | i >= 0    = unpack $ fromMaybe (pack errorString) a
  | otherwise = errorString
  where
    a :: Maybe ByteString
    a = join $ bs !? i

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
showTermWithBinders bs (IdFam t)                     = "=[" ++ showTermWithBinders bs t ++ "]"
showTermWithBinders bs (Id (Just t) m n)             = showTermWithBinders bs m ++ " =[" ++ showTermWithBinders bs t ++ "] " ++ showTermWithBinders bs n
showTermWithBinders bs (Id Nothing m n)              = showTermWithBinders bs m ++ " = " ++ showTermWithBinders bs n
showTermWithBinders bs (Sum m n)                     = showTermWithBinders bs m ++ " + " ++ showTermWithBinders bs n
showTermWithBinders bs (Lam (x, Just t) m)           = "\\(" ++ unpack x ++ " : " ++ showTermWithBinders bs t ++ "). " ++ showTermWithBinders (Just x : bs) m
showTermWithBinders bs (Lam (x, Nothing) m)          = "\\" ++ unpack x ++ ". " ++ showTermWithBinders (Just x : bs) m
showTermWithBinders bs (Univ 0)                      = "U"
showTermWithBinders bs (Univ i)                      = "U" ++ show i
showTermWithBinders bs Bot                           = "_|_"
showTermWithBinders bs Top                           = "T"
showTermWithBinders bs Nat                           = "Nat"
showTermWithBinders bs Zero                          = "0"
showTermWithBinders bs (Inl m)                       = "inl(" ++ showTermWithBinders bs m ++ ")"
showTermWithBinders bs (Inr m)                       = "inr(" ++ showTermWithBinders bs m ++ ")"
showTermWithBinders bs (Refl m)                      = "refl[" ++ showTermWithBinders bs m ++ "]"
showTermWithBinders bs (Funext p)                    = "funext(" ++ showTermWithBinders bs p ++ ")"
showTermWithBinders bs (Univalence a)                = "univalence(" ++ showTermWithBinders bs a ++ ")"
showTermWithBinders bs (Sigma (Just x, t) m)         = "(" ++ unpack x ++ " : " ++ showTermWithBinders bs t ++ ") x " ++ showSigmaOperarands (Just x : bs) m
showTermWithBinders bs (Sigma (Nothing, t) m)        = showSigmaOperarands bs t ++ " x " ++ showSigmaOperarands (Nothing : bs) m
showTermWithBinders bs (Pi (x, t, ex) m)             = showPi bs (Pi (x, t, ex) m)
  where
    showPi :: Binders -> Term -> String
    showPi bs (Pi (Nothing, Pi (y, t, ex') m, ex) n) = getExLParen ex ++ showPi bs (Pi (y, t, ex') m) ++ getExRParen ex ++ " -> " ++ showTermWithBinders (Nothing : bs) n
    showPi bs (Pi (Just x, t, ex) m)                 = getExLParen ex ++ unpack x ++ " : " ++ showTermWithBinders bs t ++ getExRParen ex ++ " -> " ++ showTermWithBinders (Just x : bs) m
    showPi bs (Pi (Nothing, t, ex) m)                = showTermWithBinders bs t ++ " -> " ++ showTermWithBinders (Nothing : bs) m

    getExLParen :: Explicitness -> String
    getExLParen Exp = "("
    getExLParen Imp = "{"

    getExRParen :: Explicitness -> String
    getExRParen Exp = ")"
    getExRParen Imp = "}"
showTermWithBinders bs (Succ m)
  | isNum m   = showNum (Succ m)
  | otherwise = showNonNum bs (Succ m)
  where
    isNum :: Term -> Bool
    isNum Zero     = True
    isNum (Succ m) = isNum m
    isNum _        = False

    showNum :: Term -> String
    showNum m = go m 0
      where
        go :: Term -> Integer -> String
        go Zero     i = show i
        go (Succ m) i = go m (i + 1)
        go _        _ = "ERROR"

    showNonNum :: Binders -> Term -> String
    showNonNum bs (Succ m) = "succ(" ++ showTermWithBinders bs m ++ ")"
    showNonNum bs _        = showNonNum bs m
showTermWithBinders bs (Ind t m c a)                 = "ind[" ++ showTermWithBinders bs t ++ "](" ++ showBoundTermWithBinders bs m ++ (if null c then "" else ", ") ++ showBoundTermsNoParen bs c ++ ", " ++ showTermWithBinders bs a ++ ")"
  where
    showBoundTermsNoParen :: Binders -> [BoundTerm] -> String
    showBoundTermsNoParen bs []     = ""
    showBoundTermsNoParen bs [y]    = showBoundTermWithBinders bs y
    showBoundTermsNoParen bs (y:ys) = showBoundTermWithBinders bs y ++ ", " ++ showBoundTermsNoParen bs ys

-- TODO: Generalise this to support arbitrary terms with any precedence
showSigmaOperarands :: Binders -> Term -> String
showSigmaOperarands bs (App m n)   = "(" ++ showTermWithBinders bs (App m n) ++ ")"
showSigmaOperarands bs (Pi t m)    = "(" ++ showTermWithBinders bs (Pi t m) ++ ")"
showSigmaOperarands bs (Sigma t m) = "(" ++ showTermWithBinders bs (Sigma t m) ++ ")"
showSigmaOperarands bs (Sum m n)   = "(" ++ showTermWithBinders bs (Sum m n) ++ ")"
showSigmaOperarands bs (Id mt m n) = "(" ++ showTermWithBinders bs (Id mt m n) ++ ")"
showSigmaOperarands bs m           = showTermWithBinders bs m

showBoundTermWithBinders :: Binders -> BoundTerm -> String
showBoundTermWithBinders bs (NoBind m)        = showTermWithBinders bs m
showBoundTermWithBinders bs (Bind (Just x) m) = unpack x ++ ". " ++ showBoundTermWithBinders (Just x : bs) m
showBoundTermWithBinders bs (Bind Nothing m)  = showBoundTermWithBinders (Nothing : bs) m

instance Show Term where
  show = showTermWithBinders binders
    where
      -- TODO: Ensure these are fresh
      binders :: [Maybe ByteString]
      binders = [Just $ pack ("a" ++ show i) | i <- [0..]]

instance Show BoundTerm where
  show = showBoundTermWithBinders binders
    where
      -- TODO: Ensure these are fresh
      binders :: [Maybe ByteString]
      binders = [Just $ pack ("a" ++ show i) | i <- [0..]]
