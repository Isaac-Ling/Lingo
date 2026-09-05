module IO.Pretty where

import Core.Term
import Core.Judgement.Utils
import Core.Judgement.Context
import Core.Judgement.Evaluation

import Control.Monad (join)
import Data.Maybe (fromMaybe)
import Data.List ((!?), intercalate)
import Data.ByteString.Lazy.Char8 (ByteString, pack, unpack)

showTermWithBindersWithImplicits :: Binders -> Term -> String
showTermWithBindersWithImplicits = showTermWithBinders True

showTermWithBindersWithoutImplicits :: Binders -> Term -> String
showTermWithBindersWithoutImplicits = showTermWithBinders False

showTermWithBinders :: Bool -> Binders -> Term -> String
showTermWithBinders b bs (Var (Free x))                = unpack x
showTermWithBinders b bs (Var (Meta i))
  | i >= 0    = "?" ++ vars !! i
  | otherwise = errorString
  where
    vars :: [String]
    vars = [show i | i <- [0..]]
    
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
showTermWithBinders b bs (App (Lam xt m) (n, ex))                = "(" ++ showTermWithBinders b bs (Lam xt m) ++ ") " ++ showExLParenOrNone ex ++ showTermWithBinders b bs n ++ showExRParenOrNone ex
showTermWithBinders b bs (App m (Lam xt n, ex))                 = showTermWithBinders b bs m ++ " " ++ showExLParen ex ++ showTermWithBinders b bs (Lam xt n) ++ showExRParen ex
showTermWithBinders b bs (App m (App p n, ex))                  = showTermWithBinders b bs m ++ " " ++ showExLParen ex ++ showTermWithBinders b bs (App p n) ++ showExRParen ex
showTermWithBinders b bs (App m (Sigma xt n, ex))               = showTermWithBinders b bs m ++ " " ++ showExLParen ex ++ showTermWithBinders b bs (Sigma xt n) ++ showExRParen ex
showTermWithBinders b bs (App m (Sum x y, ex))                  = showTermWithBinders b bs m ++ " " ++ showExLParen ex ++ showTermWithBinders b bs (Sum x y) ++ showExRParen ex
showTermWithBinders b bs (App m (Pi xt n, ex))                  = showTermWithBinders b bs m ++ " " ++ showExLParen ex ++ showTermWithBinders b bs (Pi xt n) ++ showExRParen ex
showTermWithBinders b bs (App m (Id t a b', ex))                = showTermWithBinders b bs m ++ " " ++ showExLParen ex ++ showTermWithBinders b bs (Id t a b') ++ showExRParen ex
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
showTermWithBinders b bs (Univ u)                               = show u
showTermWithBinders b bs Bot                                    = "_|_"
showTermWithBinders b bs Top                                    = "T"
showTermWithBinders b bs Nat                                    = "Nat"
showTermWithBinders b bs Zero                                   = "0"
showTermWithBinders b bs (Inl m)                                = "inl(" ++ showTermWithBinders b bs m ++ ")"
showTermWithBinders b bs (Inr m)                                = "inr(" ++ showTermWithBinders b bs m ++ ")"
showTermWithBinders b bs (Refl Nothing)                         = "refl"
showTermWithBinders b bs (Refl (Just m))                        = "refl[" ++ showTermWithBinders b bs m ++ "]"
showTermWithBinders b bs (Funext p)                             = "funext(" ++ showTermWithBinders b bs p ++ ")"
showTermWithBinders b bs (Univalence a)                         = "univalence(" ++ showTermWithBinders b bs a ++ ")"
showTermWithBinders b bs (Sigma (Just x, t) m)                  = "(" ++ unpack x ++ " : " ++ showTermWithBinders b bs t ++ ") x " ++ showSigmaOperarands b (Just x : bs) m
showTermWithBinders b bs (Sigma (Nothing, Sigma x n) m)         = "(" ++ showTermWithBinders b bs (Sigma x n) ++ ") x " ++ showSigmaOperarands b (Nothing : bs) m
showTermWithBinders b bs (Sigma (Nothing, t) m)                 = showSigmaOperarands b bs t ++ " x " ++ showSigmaOperarands b (Nothing : bs) m
showTermWithBinders False bs (Pi (Just x, t, Imp) m)            = showTermWithBinders False (Just x : bs) m
showTermWithBinders False bs (Pi (Nothing, t, Imp) m)           = showTermWithBinders False (Nothing : bs) m
showTermWithBinders b bs (Pi (Nothing, Pi (y, t, ex') m, ex) n) = showExLParen ex ++ showTermWithBinders b bs (Pi (y, t, ex') m) ++ showExRParen ex ++ " -> " ++ showTermWithBinders b (Nothing : bs) n
showTermWithBinders b bs
  (Pi (Just x, t, ex)
  (Pi (Just y, t', ex') m))
    | equalOrMetaUniv t (bumpDown t') && ex == ex'              = showIteratedPis (Just y : Just x : bs) ex t [y, x] m
  where
    showIteratedPis :: Binders -> Explicitness -> Term -> [ByteString] -> Term -> String
    showIteratedPis bs' ex t vars (Pi (Just x, t', ex') m)
      | equalOrMetaUniv t (shift (-(length vars)) t') && ex == ex' = showIteratedPis (Just x : bs') ex t (x : vars) m
    showIteratedPis bs' ex t vars m                                = showExLParen ex ++ intercalate ", " (reverse $ map unpack vars) ++ " : " ++ showTermWithBinders b bs t ++ showExRParen ex ++ " -> " ++ showTermWithBinders b bs' m

    equalOrMetaUniv :: Term -> Term -> Bool
    equalOrMetaUniv (Univ (UParam _)) (Univ (UParam _)) = True
    equalOrMetaUniv m n                                 = m == n
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

showTermWithContext :: BoundContext -> Term -> String
showTermWithContext bctx = showTermWithBindersWithImplicits (map fst bctx)

showTermWithContextWithoutImplicits :: BoundContext -> Term -> String
showTermWithContextWithoutImplicits bctx = showTermWithBindersWithoutImplicits (map fst bctx)

instance Show Term where
  show = showTermWithBinders True binders
    where
      binders :: [Maybe ByteString]
      binders = [Just $ pack ("!a" ++ show i) | i <- [0..]]

instance Show Universe where
  show UFlex      = "U"
  show (UParam i) = "U"
  show (UVar i)   = "U?" ++ show i
  show (ULvl i)   = "U" ++ show i

instance Show UnivConstraint where
  show (ULeq u v) = show u ++ " <= " ++ show v
  show (ULt u v)  = show u ++ " < " ++ show v

instance Show TermData where
  show td = "{ " ++  show (eterm td) ++ ", " ++ show (ecsts td) ++ " }"

instance Show BoundTerm where
  show = showBoundTermWithBinders True binders
    where
      binders :: [Maybe ByteString]
      binders = [Just $ pack ("!b" ++ show i) | i <- [0..]]
