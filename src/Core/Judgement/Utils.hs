module Core.Judgement.Utils where

import Core.Term
import Core.Error

import Data.Set (Set)
import Control.Monad (join)
import Data.List (elemIndex, (!?))
import Data.Maybe (fromMaybe)
import Data.ByteString.Lazy.Char8 (ByteString, pack, unpack)
import qualified Data.Set as Set

-- A list of binders, where the ith element is the ith binder away from the
-- current term. Nothing is used if we should never match against that binder
type Binders = [Maybe ByteString]

-- TODO: Add implicit lambdas inside sub-terms ??
elaborateSource :: SourceTerm -> SourceTerm -> SourceTerm
elaborateSource (SLam (x, t, Imp) m) (SPi (_, _, Imp) n) = SLam (x, t, Imp) $ elaborateSource m n
elaborateSource m (SPi (Just x, t, Imp) n)               = SLam (x, Just t, Imp) $ elaborateSource m n
elaborateSource (SLam (x, t, Exp) m) (SPi (_, _, Exp) n) = SLam (x, t, Exp) $ elaborateSource m n
elaborateSource m _                                      = m

toDeBruijn :: SourceTerm -> Term
toDeBruijn = go []
  where
    go :: Binders -> SourceTerm -> Term
    go bs (SVar x)              = case elemIndex (Just x) bs of
      Just i  -> Var (Bound i)
      Nothing -> Var (Free x)
    go bs (SLam (x, Nothing, ex) m) = Lam (x, Nothing, ex) (go (Just x : bs) m)
    go bs (SLam (x, Just t, ex) m)  = Lam (x, Just $ go bs t, ex) (go (Just x : bs) m)
    go bs (SPi (x, t, ex) m)        = Pi (x, go bs t, ex) (go (x : bs) m)
    go bs (SSigma (x, t) m)         = Sigma (x, go bs t) (go (x : bs) m)
    go bs (SApp m (n, ex))          = App (go bs m) (go bs n, ex)
    go bs (SPair m n)               = Pair (go bs m) (go bs n)
    go bs (SSum m n)                = Sum (go bs m) (go bs n)
    go bs (SIdFam t)                = IdFam $ go bs t
    go bs (SId t m n)               = Id (fmap (go bs) t) (go bs m) (go bs n)
    go bs (SInd t m c a)            = Ind (go bs t) (boundTermToDeBruijn bs m) (map (boundTermToDeBruijn bs) c) (go bs a)
    go bs (SUniv i)                 = Univ i
    go bs SBot                      = Bot
    go bs STop                      = Top
    go bs SNat                      = Nat
    go bs SZero                     = Zero
    go bs (SSucc m)                 = Succ $ go bs m
    go bs (SInl m)                  = Inl $ go bs m
    go bs (SInr m)                  = Inr $ go bs m
    go bs (SFunext p)               = Funext $ go bs p
    go bs (SUnivalence f)           = Univalence $ go bs f
    go bs (SRefl m)                 = Refl $ go bs m
    go bs SStar                     = Star

    boundTermToDeBruijn :: Binders -> SourceBoundTerm -> BoundTerm
    boundTermToDeBruijn bs (SNoBind m) = NoBind $ go bs m
    boundTermToDeBruijn bs (SBind x m) = Bind (Just x) $ boundTermToDeBruijn (Just x : bs) m

resolve :: Environment -> Term -> Term
resolve env (Var (Free x))           = case lookup x env of
  Just m  -> resolve env m
  Nothing -> Var $ Free x
resolve env (Var (Meta i sp))        = Var $ Meta i sp
resolve env (Var (Bound i))          = Var $ Bound i
resolve env (Lam (x, Nothing, ex) m) = Lam (x, Nothing, ex) (resolve env m)
resolve env (Lam (x, Just t, ex) m)  = Lam (x, Just $ resolve env t, ex) (resolve env m)
resolve env (Pi (x, t, ex) m)        = Pi (x, resolve env t, ex) (resolve env m)
resolve env (Sigma (x, t) m)         = Sigma (x, resolve env t) (resolve env m)
resolve env (App m (n, ex))          = App (resolve env m) (resolve env n, ex)
resolve env (Pair m n)               = Pair (resolve env m) (resolve env n)
resolve env (Sum m n)                = Sum (resolve env m) (resolve env n)
resolve env (Inl m)                  = Inl $ resolve env m
resolve env (Inr m)                  = Inr $ resolve env m
resolve env (Refl m)                 = Refl $ resolve env m
resolve env (Succ m)                 = Succ $ resolve env m
resolve env (IdFam t)                = IdFam $ resolve env t
resolve env (Funext p)               = Funext $ resolve env p
resolve env (Univalence a)           = Univalence $ resolve env a
resolve env (Id mt m n)              = Id (fmap (resolve env) mt) (resolve env m) (resolve env n)
resolve env (Ind t m c a)            = Ind (resolve env t) (resolveBoundTerm env m) (map (resolveBoundTerm env) c) (resolve env a)
  where
    resolveBoundTerm :: Environment -> BoundTerm -> BoundTerm
    resolveBoundTerm env (NoBind m) = NoBind $ resolve env m
    resolveBoundTerm env (Bind x m) = Bind x $ resolveBoundTerm env m
resolve env m                        = m

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
    go k l (Var (Meta i sp))        = Var $ Meta i $ map (go k l) sp
    go k l (Lam (x, Nothing, ex) m) = Lam (x, Nothing, ex) (go k (l + 1) m)
    go k l (Lam (x, Just t, ex) m)  = Lam (x, Just $ go k l t, ex) (go k (l + 1) m)
    go k l (Pi (x, t, ex) m)        = Pi (x, go k l t, ex) (go k (l + 1) m)
    go k l (Sigma (x, t) m)         = Sigma (x, go k l t) (go k (l + 1) m)
    go k l (App m (n, ex))          = App (go k l m) (go k l n, ex)
    go k l (Pair m n)               = Pair (go k l m) (go k l n)
    go k l (Sum m n)                = Sum (go k l m) (go k l n)
    go k l (IdFam t)                = IdFam (go k l t)
    go k l (Id mt m n)              = Id (fmap (go k l) mt) (go k l m) (go k l n)
    go k l (Inl m)                  = Inl $ go k l m
    go k l (Inr m)                  = Inr $ go k l m
    go k l (Succ m)                 = Succ $ go k l m
    go k l (Refl m)                 = Refl $ go k l m
    go k l (Funext p)               = Funext $ go k l p
    go k l (Univalence a)           = Funext $ go k l a
    go k l (Ind t m c a)            = Ind (go k l t) (shiftInBoundTerm k l m) (map (shiftInBoundTerm k l) c) (go k l a)
    go k l m                        = m

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
openFor m k (Var (Meta i sp))        = Var $ Meta i $ map (openFor m k) sp
openFor m k (Lam (x, Just t, ex) n)  = Lam (x, Just $ openFor m k t, ex) (openFor (bumpUp m) (k + 1) n)
openFor m k (Lam (x, Nothing, ex) n) = Lam (x, Nothing, ex) (openFor (bumpUp m) (k + 1) n)
openFor m k (Pi (x, t, ex) n)        = Pi (x, openFor m k t, ex) (openFor (bumpUp m) (k + 1) n)
openFor m k (Sigma (x, t) n)         = Sigma (x, openFor m k t) (openFor (bumpUp m) (k + 1) n)
openFor m k (Pair t n)               = Pair (openFor m k t) (openFor m k n)
openFor m k (IdFam t)                = IdFam $ openFor m k t
openFor m k (Id mt t n)              = Id (fmap (openFor m k) mt) (openFor m k t) (openFor m k n)
openFor m k (Sum t n)                = Sum (openFor m k t) (openFor m k n)
openFor m k (App t (n, ex))          = App (openFor m k t) (openFor m k n, ex)
openFor m k (Inl n)                  = Inl $ openFor m k n
openFor m k (Inr n)                  = Inr $ openFor m k n
openFor m k (Refl n)                 = Refl $ openFor m k n
openFor m k (Succ n)                 = Succ $ openFor m k n
openFor m k (Funext p)               = Funext $ openFor m k p
openFor m k (Univalence a)           = Univalence $ openFor m k a
openFor m k (Ind t m' c a)           = Ind (openFor m k t) (openInBoundTerm m k m') (map (openInBoundTerm m k) c) (openFor m k a)
  where
    openInBoundTerm :: Term -> Int -> BoundTerm -> BoundTerm
    openInBoundTerm m k (NoBind n) = NoBind (openFor m k n)
    openInBoundTerm m k (Bind x n) = Bind x (openInBoundTerm (bumpUp m) (k + 1) n)
openFor m k n                        = n

-- Returns True if there is a variable bound to a 0 index binder in the given term
isBinderUsed :: Term -> Bool
isBinderUsed = go 0
  where
    go :: Int -> Term -> Bool
    go k (Var (Bound i))
      | i == k    = True
      | otherwise = False
    go k (Lam (x, Just t, _) n)  = go k t || go (k + 1) n
    go k (Lam (x, Nothing, _) n) = go (k + 1) n
    go k (Pi (x, t, _) n)        = go k t || go (k + 1) n
    go k (Sigma (x, t) n)        = go k t || go (k + 1) n
    go k (Pair t n)              = go k t || go k n
    go k (App t (n, _))          = go k t || go k n
    go k (Id mt m n)             = maybe False (go k) mt || go k m || go k n
    go k (Refl m)                = go k m
    go k (Funext m)              = go k m
    go k (Univalence m)          = go k m
    go k (Succ m)                = go k m
    go k (Inl m)                 = go k m
    go k (Inr m)                 = go k m
    go k (IdFam m)               = go k m
    go k (Ind t m' c a)          = go k t || isBinderUsedInBoundTerm k m' || any (isBinderUsedInBoundTerm k) c || go k a
    go k n                       = False

    isBinderUsedInBoundTerm :: Int -> BoundTerm -> Bool
    isBinderUsedInBoundTerm k (NoBind n) = go k n
    isBinderUsedInBoundTerm k (Bind x n) = isBinderUsedInBoundTerm (k + 1) n

getMetasInTerm :: Term -> Set Int
getMetasInTerm (Var (Meta i _))        = Set.singleton i
getMetasInTerm (Lam (x, Just t, _) n)  = getMetasInTerm t <> getMetasInTerm n
getMetasInTerm (Lam (x, Nothing, _) n) = getMetasInTerm n
getMetasInTerm (Pi (x, t, _) n)        = getMetasInTerm t <> getMetasInTerm n
getMetasInTerm (Sigma (x, t) n)        = getMetasInTerm t <> getMetasInTerm n
getMetasInTerm (Pair t n)              = getMetasInTerm t <> getMetasInTerm n
getMetasInTerm (App t (n, _))          = getMetasInTerm t <> getMetasInTerm n
getMetasInTerm (Id mt m n)             = maybe Set.empty getMetasInTerm mt <> getMetasInTerm m <> getMetasInTerm n
getMetasInTerm (Refl m)                = getMetasInTerm m
getMetasInTerm (Funext m)              = getMetasInTerm m
getMetasInTerm (Univalence m)          = getMetasInTerm m
getMetasInTerm (Succ m)                = getMetasInTerm m
getMetasInTerm (Inl m)                 = getMetasInTerm m
getMetasInTerm (Inr m)                 = getMetasInTerm m
getMetasInTerm (IdFam m)               = getMetasInTerm m
getMetasInTerm (Ind t m' c a)          = getMetasInTerm t <> getMetasInBoundTerm m' <> Set.unions (map getMetasInBoundTerm c) <> getMetasInTerm a
  where
    getMetasInBoundTerm :: BoundTerm -> Set Int
    getMetasInBoundTerm (NoBind m) = getMetasInTerm m
    getMetasInBoundTerm (Bind _ m) = getMetasInBoundTerm m
getMetasInTerm m                       = Set.empty

containsMeta :: Term -> Bool
containsMeta = not . Set.null . getMetasInTerm

isRigid :: Term -> Bool
isRigid (Var (Meta _ _)) = False
isRigid (App m _)        = isRigid m
isRigid _                = True

isFlex :: Term -> Bool
isFlex = not . isRigid

showTermWithBindersWithImplicits :: Binders -> Term -> String
showTermWithBindersWithImplicits = showTermWithBinders True

showTermWithBindersWithoutImplicits :: Binders -> Term -> String
showTermWithBindersWithoutImplicits = showTermWithBinders False

showTermWithBinders :: Bool -> Binders -> Term -> String
showTermWithBinders b bs (Var (Free x))                = unpack x
showTermWithBinders b bs (Var (Meta i sp))
  | i >= 0    = "?" ++ vars !! i
  | otherwise = errorString
  where
    vars :: [String]
    vars = ["a" ++ show i | i <- [0..]]
    
    errorString :: String
    errorString = "!ERROR"
showTermWithBinders b bs (Var (Bound i))
  | i >= 0    = unpack $ fromMaybe (pack errorString) a
  | otherwise = errorString
  where
    a :: Maybe ByteString
    a = join $ bs !? i

    errorString :: String
    errorString = "!ERROR"
showTermWithBinders b bs Star                                   = "*"
showTermWithBinders False bs (App m (n, Imp))                   = showTermWithBinders False bs m
showTermWithBinders b bs (App (Lam xt m) (Lam yt n, ex))        = "(" ++ showTermWithBinders b bs (Lam xt m) ++ ") " ++ showExLParen ex ++ showTermWithBinders b bs (Lam yt n) ++ showExRParen ex
showTermWithBinders b bs (App (Lam xt m) (App p n, ex))         = "(" ++ showTermWithBinders b bs (Lam xt m) ++ ") " ++ showExLParen ex ++ showTermWithBinders b bs (App p n) ++ showExRParen ex
showTermWithBinders b bs (App m (Lam xt n, ex))                 = showTermWithBinders b bs m ++ " " ++ showExLParen ex ++ showTermWithBinders b bs (Lam xt n) ++ showExRParen ex
showTermWithBinders b bs (App m (App p n, ex))                  = showTermWithBinders b bs m ++ " " ++ showExLParen ex ++ showTermWithBinders b bs (App p n) ++ showExRParen ex
showTermWithBinders b bs (App m (Sigma xt n, ex))               = showTermWithBinders b bs m ++ " " ++ showExLParen ex ++ showTermWithBinders b bs (Sigma xt n) ++ showExRParen ex
showTermWithBinders b bs (App (Pi xt m) (n, ex))                = "(" ++ showTermWithBinders b bs (Pi xt m) ++ ") " ++ showTermWithBinders b bs n
showTermWithBinders b bs (App (Sigma xt m) (n, ex))             = "(" ++ showTermWithBinders b bs (Sigma xt m) ++ ") " ++ showExLParenOrNone ex ++ showTermWithBinders b bs n ++ showExRParenOrNone ex
showTermWithBinders b bs (App m (n, ex))                        = showTermWithBinders b bs m ++ " " ++ showExLParenOrNone ex ++ showTermWithBinders b bs n ++ showExRParenOrNone ex
showTermWithBinders b bs (Pair m n)                             = "(" ++ showTermWithBinders b bs m ++ ", " ++ showPairElement b bs n ++  ")"
  where
    showPairElement :: Bool -> Binders -> Term -> String
    showPairElement b bc (Pair m n) = showTermWithBinders b bc m ++ ", " ++ showPairElement b bc n
    showPairElement b bc m          = showTermWithBinders b bc m
showTermWithBinders b bs (IdFam t)                              = "=[" ++ showTermWithBinders b bs t ++ "]"
showTermWithBinders b bs (Id (Just t) m n)                      = showTermWithBinders b bs m ++ " =[" ++ showTermWithBinders b bs t ++ "] " ++ showTermWithBinders b bs n
showTermWithBinders b bs (Id Nothing m n)                       = showTermWithBinders b bs m ++ " = " ++ showTermWithBinders b bs n
showTermWithBinders b bs (Sum m n)                              = showTermWithBinders b bs m ++ " + " ++ showTermWithBinders b bs n
showTermWithBinders False bs (Lam (x, Just t, Imp) m)           = showTermWithBinders False (Just x : bs) m
showTermWithBinders b bs (Lam (x, Just t, ex) m)                = "\\" ++ showExLParen ex ++ unpack x ++ " : " ++ showTermWithBinders b bs t ++ showExRParen ex ++ ". " ++ showTermWithBinders b (Just x : bs) m
showTermWithBinders False bs (Lam (x, Nothing, Imp) m)          = showTermWithBinders False (Just x : bs) m
showTermWithBinders b bs (Lam (x, Nothing, ex) m)               = "\\" ++ showExLParenOrNone ex ++ unpack x ++ showExRParenOrNone ex ++ ". " ++ showTermWithBinders b (Just x : bs) m
showTermWithBinders b bs (Univ 0)                               = "U"
showTermWithBinders b bs (Univ i)                               = "U" ++ show i
showTermWithBinders b bs Bot                                    = "_|_"
showTermWithBinders b bs Top                                    = "T"
showTermWithBinders b bs Nat                                    = "Nat"
showTermWithBinders b bs Zero                                   = "0"
showTermWithBinders b bs (Inl m)                                = "inl(" ++ showTermWithBinders b bs m ++ ")"
showTermWithBinders b bs (Inr m)                                = "inr(" ++ showTermWithBinders b bs m ++ ")"
showTermWithBinders b bs (Refl m)                               = "refl[" ++ showTermWithBinders b bs m ++ "]"
showTermWithBinders b bs (Funext p)                             = "funext(" ++ showTermWithBinders b bs p ++ ")"
showTermWithBinders b bs (Univalence a)                         = "univalence(" ++ showTermWithBinders b bs a ++ ")"
showTermWithBinders b bs (Sigma (Just x, t) m)                  = "(" ++ unpack x ++ " : " ++ showTermWithBinders b bs t ++ ") x " ++ showSigmaOperarands b (Just x : bs) m
showTermWithBinders b bs (Sigma (Nothing, Sigma x n) m)         = "(" ++ showTermWithBinders b bs (Sigma x n) ++ ") x " ++ showSigmaOperarands b (Nothing : bs) m
showTermWithBinders b bs (Sigma (Nothing, t) m)                 = showSigmaOperarands b bs t ++ " x " ++ showSigmaOperarands b (Nothing : bs) m
showTermWithBinders False bs (Pi (Just x, t, Imp) m)            = showTermWithBinders False (Just x : bs) m
showTermWithBinders False bs (Pi (Nothing, t, Imp) m)           = showTermWithBinders False (Nothing : bs) m
showTermWithBinders b bs (Pi (Nothing, Pi (y, t, ex') m, ex) n) = showExLParen ex ++ showTermWithBinders b bs (Pi (y, t, ex') m) ++ showExRParen ex ++ " -> " ++ showTermWithBinders b (Nothing : bs) n
showTermWithBinders b bs (Pi (Just x, t, ex) m)                 = showExLParen ex ++ unpack x ++ " : " ++ showTermWithBinders b bs t ++ showExRParen ex ++ " -> " ++ showTermWithBinders b (Just x : bs) m
showTermWithBinders b bs (Pi (Nothing, t, ex) m)                = showTermWithBinders b bs t ++ " -> " ++ showTermWithBinders b (Nothing : bs) m

showTermWithBinders b bs (Succ m)
  | isNum m   = showNum (Succ m)
  | otherwise = showNonNum b bs (Succ m)
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
        go _        _ = "!ERROR"

    showNonNum :: Bool -> Binders -> Term -> String
    showNonNum b bs (Succ m) = "succ(" ++ showTermWithBinders b bs m ++ ")"
    showNonNum b bs _        = showNonNum b bs m
showTermWithBinders b bs (Ind t m c a)                 = "ind[" ++ showTermWithBinders b bs t ++ "](" ++ showBoundTermWithBinders b bs m ++ (if null c then "" else ", ") ++ showBoundTermsNoParen b bs c ++ ", " ++ showTermWithBinders b bs a ++ ")"
  where
    showBoundTermsNoParen :: Bool -> Binders -> [BoundTerm] -> String
    showBoundTermsNoParen b bs []     = ""
    showBoundTermsNoParen b bs [y]    = showBoundTermWithBinders b bs y
    showBoundTermsNoParen b bs (y:ys) = showBoundTermWithBinders b bs y ++ ", " ++ showBoundTermsNoParen b bs ys

showExLParen :: Explicitness -> String
showExLParen Exp = "("
showExLParen Imp = "{"

showExLParenOrNone :: Explicitness -> String
showExLParenOrNone Exp = ""
showExLParenOrNone Imp = "{"

showExRParen :: Explicitness -> String
showExRParen Exp = ")"
showExRParen Imp = "}"

showExRParenOrNone :: Explicitness -> String
showExRParenOrNone Exp = ""
showExRParenOrNone Imp = "}"

-- TODO: Generalise this to support arbitrary terms with any precedence
showSigmaOperarands :: Bool -> Binders -> Term -> String
showSigmaOperarands b bs (App m n)   = "(" ++ showTermWithBinders b bs (App m n) ++ ")"
showSigmaOperarands b bs (Pi t m)    = "(" ++ showTermWithBinders b bs (Pi t m) ++ ")"
showSigmaOperarands b bs (Sum m n)   = "(" ++ showTermWithBinders b bs (Sum m n) ++ ")"
showSigmaOperarands b bs (Id mt m n) = "(" ++ showTermWithBinders b bs (Id mt m n) ++ ")"
showSigmaOperarands b bs m           = showTermWithBinders b bs m

showBoundTermWithBinders :: Bool -> Binders -> BoundTerm -> String
showBoundTermWithBinders b bs (NoBind m)        = showTermWithBinders b bs m
showBoundTermWithBinders b bs (Bind (Just x) m) = unpack x ++ ". " ++ showBoundTermWithBinders b (Just x : bs) m
showBoundTermWithBinders b bs (Bind Nothing m)  = showBoundTermWithBinders b (Nothing : bs) m

showTermWithoutImplicits :: Term -> String
showTermWithoutImplicits = showTermWithBinders False binders
  where
    binders :: [Maybe ByteString]
    binders = [Just $ pack ("!a" ++ show i) | i <- [0..]]

instance Show Term where
  show = showTermWithBinders True binders
    where
      binders :: [Maybe ByteString]
      binders = [Just $ pack ("!a" ++ show i) | i <- [0..]]

instance Show BoundTerm where
  show = showBoundTermWithBinders True binders
    where
      binders :: [Maybe ByteString]
      binders = [Just $ pack ("!b" ++ show i) | i <- [0..]]
