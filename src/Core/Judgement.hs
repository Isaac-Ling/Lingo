module Core.Judgement where

import Core.Data
import Core.Error

import Data.ByteString.Lazy.Char8 (ByteString, pack, unpack)

isAlphaEquiv :: Term -> Term -> Bool
isAlphaEquiv (Var x) (Var y)                    = x == y
isAlphaEquiv (Lam (x, t) m) (Lam (y, t') n)     = isAlphaEquiv t t' && isAlphaEquiv m (sub (Var x) y n)
isAlphaEquiv (Pi (x, t) m) (Pi (y, t') n)       = isAlphaEquiv t t' && isAlphaEquiv m (sub (Var x) y n)
isAlphaEquiv (Sigma (x, t) m) (Sigma (y, t') n) = isAlphaEquiv t t' && isAlphaEquiv m (sub (Var x) y n)
isAlphaEquiv (App m n) (App m' n')              = isAlphaEquiv m m' && isAlphaEquiv n n'
isAlphaEquiv (Pair m n) (Pair m' n')            = isAlphaEquiv m m' && isAlphaEquiv n n'
isAlphaEquiv Star Star                          = True
isAlphaEquiv Zero Zero                          = True
isAlphaEquiv One One                            = True
isAlphaEquiv (Univ i) (Univ j)                  = i == j
isAlphaEquiv _ _                                = False

typeCheck :: Context -> Term -> CanError Term
typeCheck g (Univ i)                                                                  = Result (Univ (i + 1))
typeCheck g Zero                                                                      = Result (Univ 0)
typeCheck g One                                                                       = Result (Univ 0)
typeCheck g Star                                                                      = Result One
typeCheck g (Var x)                                                                   = case lookup x g of
  Just t  -> Result t
  Nothing -> Error FailedToInferType (Just ("Unknown variable " ++ show x))
typeCheck g (Pi (x, t) m)                                                             = case (typeCheck g t, typeCheck ((x, t) : g) m) of
  (Result (Univ i), Result (Univ j)) -> Result (Univ (max i j))
  (Result (Univ i), Result _)        -> Error TypeMismatch (Just (show m ++ " is not a term of a universe"))
  (Result _, Result _)               -> Error TypeMismatch (Just (show t ++ " is not a term of a universe"))
  (Error errc s, _)                  -> Error errc s
  (_, Error errc s)                  -> Error errc s
typeCheck g (Sigma (x, t) m)                                                          = case (typeCheck g t, typeCheck ((x, t) : g) m) of
  (Result (Univ i), Result (Univ j)) -> Result (Univ (max i j))
  (Result (Univ i), Result _)        -> Error TypeMismatch (Just (show m ++ " is not a term of a universe"))
  (Result _, Result _)               -> Error TypeMismatch (Just (show t ++ " is not a term of a universe"))
  (Error errc s, _)                  -> Error errc s
  (_, Error errc s)                  -> Error errc s
typeCheck g (Lam (x, t) m)                                                            = case (typeCheck g t, typeCheck ((x, t) : g) m) of
  (Result (Univ _), Result t') -> Result (Pi (x, t) t')
  (Result _, Result _)         -> Error TypeMismatch (Just (show t ++ " is not a term of a universe"))
  (Error errc s, _)            -> Error errc s
  (_, Error errc s)            -> Error errc s
typeCheck g (App m n)                                                                 = case (typeCheck g m, typeCheck g n) of
  (Result (Pi (x, t) t'), Result t'') -> if t == t'' then Result (sub n x t') else Error TypeMismatch (Just ("Type " ++ show (Pi (x, t) t') ++ " cannot be applied to type " ++ show t''))
  (Result _, Result _)                -> Error TypeMismatch (Just (show m ++ " is not a Pi type") )
  (Error errc s, _)                   -> Error errc s
  (_, Error errc s)                   -> Error errc s
-- TODO: This only supports non-dependent pairs, generalise it
typeCheck g (Pair m n)                    = case (typeCheck g m, typeCheck g n) of
  (Result t, Result t') -> Result (Sigma (getFreshVar n, t) t')
  (Error errc s, _)     -> Error errc s
  (_, Error errc s)     -> Error errc s
typeCheck g (Ind Zero (NoBind m) [] a)                                                = typeCheck g (Ind Zero (Bind (getFreshVar m) (NoBind m)) [] a)
typeCheck g (Ind Zero (Bind x (NoBind m)) [] a)                                       = case (typeCheck ((x, Zero) : g) m, typeCheck g a) of
  (Result (Univ _), Result Zero) -> Result (sub a x m)
  (Result _, Result Zero)           -> Error TypeMismatch (Just (show m ++ " is not a term of a universe"))
  (Result _, Result _)              -> Error TypeMismatch (Just (show a ++ " is not of the type " ++ show Zero))
  (Error errc s, _)                 -> Error errc s
  (_, Error errc s)                 -> Error errc s
typeCheck g (Ind One (NoBind m) [NoBind c] a)                                         = typeCheck g (Ind One (Bind (getFreshVar m) (NoBind m)) [NoBind c] a)
typeCheck g (Ind One (Bind x (NoBind m)) [NoBind c] a)                                = case (typeCheck ((x, One) : g) m, typeCheck g c, typeCheck g a) of
  (Result (Univ _), Result t, Result One) -> if t == sub Star x m then Result (sub a x m) else Error TypeMismatch (Just ("The term " ++ show c ++ " does not have the type of the motive " ++ show m))
  (Result _, Result t, Result One)        -> Error TypeMismatch (Just (show m ++ " is not a term of a universe"))
  (Result _, Result _, Result _)          -> Error TypeMismatch (Just (show a ++ " is not of the type " ++ show One))
  (Error errc s, _, _)                    -> Error errc s
  (_, Error errc s, _)                    -> Error errc s
  (_, _, Error errc s)                    -> Error errc s
typeCheck g (Ind (Sigma (x, t) n) (NoBind m) [Bind w (Bind y (NoBind f))] a)          = typeCheck g (Ind (Sigma (x, t) n) (Bind (getFreshVar m) (NoBind m)) [Bind w (Bind y (NoBind f))] a)
typeCheck g (Ind (Sigma (x, t) n) (Bind z (NoBind m)) [Bind w (Bind y (NoBind f))] a) = case (typeCheck ((z, Sigma (x, t) n) : g) m, typeCheck ((w, t) : (y, n) : g) f, typeCheck g a) of
  (Result (Univ _), Result s, Result s') -> case (s == sub (Pair (Var w) (Var y)) z m, s' == Sigma (x, t) n) of
    (True, True) -> Result (sub a z m)
    (True, _)    -> Error TypeMismatch (Just ("The term " ++ show a ++ " is not of the type " ++ show (Sigma (x, t) n)))
    (_, _)       -> Error TypeMismatch (Just ("The term " ++ show g ++ " is not of the type " ++ show (sub (Pair (Var w) (Var y)) z m)))
  (Result _, Result _, Result _)        -> Error TypeMismatch (Just (show m ++ " is not a term of a universe"))
  (Error errc s, _, _)                    -> Error errc s
  (_, Error errc s, _)                    -> Error errc s
  (_, _, Error errc s)                    -> Error errc s
typeCheck g (Ind t m c a)                                                             = Error FailedToInferType (Just ("Invalid induction " ++ show (Ind t m c a)))

-- A is a type <=> A : Univ i, for some i
isType :: Context -> Term -> Bool
isType g a = case typeCheck g a of
  Result (Univ _) -> True
  _               -> False

ctx :: Context -> Bool
ctx []         = True
ctx ((_, t):g) = isType g t && ctx g


isValue :: Term -> Bool
isValue (Lam _ _) = True
isValue m         = isNeutral m

isNeutral :: Term -> Bool
isNeutral (Var _)   = True
isNeutral (App m n) = isNeutral m && isValue n
isNeutral Star      = True
isNeutral (Univ _)  = True
isNeutral Zero      = True
isNeutral One       = True
isNeutral _         = False

isFreeIn :: ByteString -> Term -> Bool
isFreeIn x (Var y)        = x == y
isFreeIn x (App m n)      = (x `isFreeIn` m) || (x `isFreeIn` n)
isFreeIn x (Lam (y, t) m)
  | x == y    = False
  | otherwise = x `isFreeIn` m || x `isFreeIn` t
isFreeIn x (Pi (y, t) m)
  | x == y    = False
  | otherwise = x `isFreeIn` m || x `isFreeIn` t
isFreeIn x (Sigma (y, t) m)
  | x == y    = False
  | otherwise = x `isFreeIn` m || x `isFreeIn` t
isFreeIn x (Ind t' m c a) = isFreeIn x t' || isFreeInBound x m || any (isFreeInBound x) c || isFreeIn x a
isFreeIn x m              = False

isFreeInBound :: ByteString -> BoundTerm -> Bool
isFreeInBound x (Bind y t) = (x /= y) && isFreeInBound x t
isFreeInBound x (NoBind t) = isFreeIn x t

-- TODO: Make fresh var readable
getFreshVar :: Term -> ByteString
getFreshVar m = buildFreshVar m (pack "a")
  where
    buildFreshVar :: Term -> ByteString -> ByteString
    buildFreshVar (Var y) x          = x <> y
    buildFreshVar (App m n) x        = buildFreshVar m x <> buildFreshVar n x
    buildFreshVar (Lam (y, _) m) x   = buildFreshVar m (x <> y)
    buildFreshVar (Pi (y, _) m) x    = buildFreshVar m (x <> y)
    buildFreshVar (Sigma (y, _) m) x = buildFreshVar m (x <> y)
    buildFreshVar (Ind t' m c a) x   = buildFreshVar t' x <> buildFreshVarInBound m x <> foldl (<>) (pack "") (map (`buildFreshVarInBound` x) c) <> buildFreshVar a x
    buildFreshVar m x                = x

    buildFreshVarInBound :: BoundTerm -> ByteString -> ByteString
    buildFreshVarInBound (NoBind m) x = buildFreshVar m x
    buildFreshVarInBound (Bind y m) x = buildFreshVarInBound m (x <> y)

sub :: Term -> ByteString -> Term -> Term
sub t x (Var y)
  | x == y             = t
  | otherwise          = Var y
sub t x (App m n)      = App (sub t x m) (sub t x n)
sub t x (Lam (y, t') m)
  | x == y         = Lam (y, t') m
  | y `isFreeIn` t = Lam (freshVar, sub t x t') (sub t x (sub (Var freshVar) y m))
  | otherwise      = Lam (y, sub t x t') (sub t x m)
  where
    freshVar :: ByteString
    freshVar = getFreshVar m
sub t x (Pi (y, t') m)
  | x == y         = Pi (y, t') m
  | y `isFreeIn` t = Pi (freshVar, sub t x t') (sub t x (sub (Var freshVar) y m))
  | otherwise      = Pi (y, sub t x t') (sub t x m)
  where
    freshVar :: ByteString
    freshVar = getFreshVar m
sub t x (Sigma (y, t') m)
  | x == y         = Sigma (y, t') m
  | y `isFreeIn` t = Sigma (freshVar, sub t x t') (sub t x (sub (Var freshVar) y m))
  | otherwise      = Sigma (y, sub t x t') (sub t x m)
  where
    freshVar :: ByteString
    freshVar = getFreshVar m
sub t x (Pair m n)     = Pair (sub t x m) (sub t x n)
sub t x (Ind t' m c a) = Ind (sub t x t') (subInBoundTerm t x m) (map (subInBoundTerm t x) c) (sub t x a)
  where
    subInBoundTerm :: Term -> ByteString -> BoundTerm -> BoundTerm
    subInBoundTerm t x (NoBind m) = NoBind (sub t x m)
    subInBoundTerm t x (Bind y m)
      | x == y         = Bind y m
      | y `isFreeIn` t = Bind freshVar (subInBoundTerm t x (subInBoundTerm (Var freshVar) y m))
      | otherwise      = Bind y (subInBoundTerm t x m)
      where
        freshVar :: ByteString
        freshVar = getFreshVar t
sub t x m              = m

beta :: Term -> Term
beta (App (Lam (x, t') m) n) = sub n x m
beta m                       = m

eval :: Environment -> Context -> Term -> CanError Term
eval e g m = case typeCheck g m of
  Result t     -> Result (unsafeEval e t)
  Error errc s -> Error errc s

unsafeEval :: Environment -> Term -> Term
unsafeEval e (Var x)                                                     = case lookup x e of
  Just m  -> unsafeEval e m
  Nothing -> Var x
unsafeEval e (Lam (x, t) (App f (Var x')))
  | x == x'   = unsafeEval e f -- Eta conversion
  | otherwise = Lam (x, unsafeEval e t) (unsafeEval e (App f (Var x')))
unsafeEval e (Lam (x, t) m)                                              = Lam (x, unsafeEval e t) (unsafeEval e m)
unsafeEval e (Pi (x, t) m)                                               = Pi (x, unsafeEval e t) (unsafeEval e m)
unsafeEval e (App m n)
  | isNeutral f = App f (unsafeEval e n)
  | otherwise   = unsafeEval e (beta (App f n))
  where
    f :: Term
    f = unsafeEval e m
unsafeEval e (Ind One _ [NoBind c] _)                                    = c
unsafeEval e (Ind (Sigma _ _) _ [Bind w (Bind y (NoBind f))] (Pair a b)) = sub a w (sub b y f)
unsafeEval e m                                                           = m

-- Judgemental equality of terms/types is alpha-beta-eta equivalence
instance Eq Term where
  m == n = isAlphaEquiv (unsafeEval [] m) (unsafeEval [] n)

instance Show Term where
  show (Var x)                          = unpack x
  show Star                             = "*"
  show (App (Lam xt m) (Lam yt n))      = "(" ++ show (Lam xt m) ++ ") " ++ "(" ++ show (Lam yt n) ++ ")"
  show (App m (Lam xt n))               = show m ++ " (" ++ show (Lam xt n) ++ ")"
  show (App m (App p n))                = show m ++ " (" ++ show (App p n) ++ ")"
  show (App (Lam xt m) n)               = "(" ++ show (Lam xt m) ++ ") " ++ show n
  show (App (Pi xt m) n)                = "(" ++ show (Pi xt m) ++ ") " ++ show n
  show (App (Sigma xt m) n)             = "(" ++ show (Sigma xt m) ++ ") " ++ show n
  show (App m n)                        = show m ++ " " ++ show n
  show (Pair m n)                       = "(" ++ show m ++ ", " ++ show n ++ ")"
  show (Lam (x, t) m)                   = "\\(" ++ unpack x ++ " : " ++ show t ++ "). " ++ show m
  show (Univ 0)                         = "U"
  show (Univ i)                         = "U" ++ show i
  show Zero                             = "0"
  show One                              = "1"
  show (Pi (x, Pi (y, t') m) n)
    | x `isFreeIn` n                    = "(" ++ unpack x ++ " : " ++ show (Pi (y, t') m) ++ ") -> " ++ show n
    | otherwise                         = "(" ++ show (Pi (y, t') m) ++ ") -> " ++ show n
  show (Pi (x, t) m)
    | x `isFreeIn` m                    = "(" ++ unpack x ++ " : " ++ show t ++ ") -> " ++ show m
    | otherwise                         = show t ++ " -> " ++ show m
  show (Sigma (x, t) (Sigma (y, t') m))
    | x `isFreeIn` Sigma (y, t') m      = "(" ++ unpack x ++ " : " ++ show t ++ ") x " ++ "(" ++ show (Sigma (y, t') m) ++ ")"
    | otherwise                         = showSigmaOperarands t ++ " x (" ++ show (Sigma (y, t') m) ++ show ")"
  show (Sigma (x, t) m)
    | x `isFreeIn` m                    = "(" ++ unpack x ++ " : " ++ show t ++ ") x " ++ showSigmaOperarands m
    | otherwise                         = showSigmaOperarands t ++ " x " ++ showSigmaOperarands m
  show (Ind t m e a)                    = "ind[" ++ show t ++ "](" ++ show m ++ (if null e then "" else ", ") ++ showListNoParen e ++ ", " ++ show a ++ ")"

showListNoParen :: Show a => [a] -> String
showListNoParen []     = ""
showListNoParen [x]    = show x
showListNoParen (x:xs) = show x ++ ", " ++ showListNoParen xs

-- TODO: Generalise this to support arbitrary terms with any precedence
showSigmaOperarands :: Term -> String
showSigmaOperarands (App m n)     = "(" ++ show (App m n) ++ ")"
showSigmaOperarands (Pi (x, t) m) = "(" ++ show (Pi (x, t) m) ++ ")"
showSigmaOperarands m             = show m

instance Show BoundTerm where
  show (Bind x t) = unpack x ++ ". " ++ show t
  show (NoBind t) = show t
