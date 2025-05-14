module Core.Judgement where

import Core.Term
import Core.Error

import Data.ByteString.Lazy.Char8 (ByteString, pack, unpack)

isAlphaEquiv :: Environment -> Term -> Term -> Bool
isAlphaEquiv e (Var x) (Var y)                            = x == y
isAlphaEquiv e (Lam (Exp (x, t)) m) (Lam (Exp (y, t')) n) = isAlphaEquiv e t t' && isAlphaEquiv e m (sub e (Var x) y n)
isAlphaEquiv e (Lam (Imp x) m) (Lam (Imp y) n)            = isAlphaEquiv e m (sub e (Var x) y n)
isAlphaEquiv e (Pi (x, t) m) (Pi (y, t') n)               = isAlphaEquiv e t t' && isAlphaEquiv e m (sub e (Var x) y n)
isAlphaEquiv e (Sigma (x, t) m) (Sigma (y, t') n)         = isAlphaEquiv e t t' && isAlphaEquiv e m (sub e (Var x) y n)
isAlphaEquiv e (App m n) (App m' n')                      = isAlphaEquiv e m m' && isAlphaEquiv e n n'
isAlphaEquiv e (Pair m n) (Pair m' n')                    = isAlphaEquiv e m m' && isAlphaEquiv e n n'
isAlphaEquiv e Star Star                                  = True
isAlphaEquiv e Zero Zero                                  = True
isAlphaEquiv e One One                                    = True
isAlphaEquiv e (Univ i) (Univ j)                          = i == j
isAlphaEquiv e (Ind t m c a) (Ind t' m' c' a')            = isAlphaEquiv e t t' && isAlphaEquivInBound e m m' && and (zipWith (isAlphaEquivInBound e) c c') && isAlphaEquiv e a a'
isAlphaEquiv e _ _                                        = False

isAlphaEquivInBound :: Environment -> BoundTerm -> BoundTerm -> Bool
isAlphaEquivInBound e (NoBind m) (NoBind n) = isAlphaEquiv e m n
isAlphaEquivInBound e (Bind a m) (Bind b n) = isAlphaEquivInBound e m (subInBoundTerm e (Var a) b n)

inferType :: Environment -> Context -> Term -> CanError Term
inferType e g (Univ i)                                                                  = Result (Univ (i + 1))
inferType e g Zero                                                                      = Result (Univ 0)
inferType e g One                                                                       = Result (Univ 0)
inferType e g Star                                                                      = Result One
inferType e g (Var x)                                                                   = case lookup x g of
  Just t  -> Result t
  Nothing -> Error FailedToInferType (Just ("Unknown variable " ++ show x))
inferType e g (Pi (x, t) m)                                                             = case (inferType e g t, inferType e ((x, t) : g) m) of
  (Result (Univ i), Result (Univ j)) -> Result (Univ (max i j))
  (Result (Univ i), Result _)        -> Error TypeMismatch (Just (show m ++ " is not a term of a universe"))
  (Result _, Result _)               -> Error TypeMismatch (Just (show t ++ " is not a term of a universe"))
  (Error errc s, _)                  -> Error errc s
  (_, Error errc s)                  -> Error errc s
inferType e g (Sigma (x, t) m)                                                          = case (inferType e g t, inferType e ((x, t) : g) m) of
  (Result (Univ i), Result (Univ j)) -> Result (Univ (max i j))
  (Result (Univ i), Result _)        -> Error TypeMismatch (Just (show m ++ " is not a term of a universe"))
  (Result _, Result _)               -> Error TypeMismatch (Just (show t ++ " is not a term of a universe"))
  (Error errc s, _)                  -> Error errc s
  (_, Error errc s)                  -> Error errc s
inferType e g (Lam (Exp (x, t)) m)                                                      = case (inferType e g t, inferType e ((x, t) : g)m) of
  (Result (Univ _), Result t') -> Result (Pi (x, t) t')
  (Result _, Result _)         -> Error TypeMismatch (Just (show t ++ " is not a term of a universe"))
  (Error errc s, _)            -> Error errc s
  (_, Error errc s)            -> Error errc s
inferType e g (Lam (Imp x) m)                                                           = Error FailedToInferType (Just ("Cannot infer type of implicit lambda " ++ show (Lam (Imp x) m)))
inferType e g (App m n)                                                                 = case (inferType e g m, inferType e g n) of
  (Result (Pi (x, t) t'), Result t'') -> if t === t'' $ e then Result (sub e n x t') else Error TypeMismatch (Just ("Type " ++ show (unsafeEval e (Pi (x, t) t')) ++ " cannot be applied to type " ++ show (unsafeEval e t'')))
  (Result _, Result _)                -> Error TypeMismatch (Just (show m ++ " is not of type Pi") )
  (Error errc s, _)                   -> Error errc s
  (_, Error errc s)                   -> Error errc s
inferType e g (Pair m n)                    = case (inferType e g m, inferType e g n) of
  (Result t, Result t') -> Result (Sigma (getFreshVar e n, t) t')
  (Error errc s, _)     -> Error errc s
  (_, Error errc s)     -> Error errc s
inferType e g (Ind Zero (NoBind m) [] a)                                                = inferType e g (Ind Zero (Bind (getFreshVar e m) (NoBind m)) [] a)
inferType e g (Ind Zero (Bind x (NoBind m)) [] a)                                       = case (inferType e ((x, Zero) : g) m, inferType e g a) of
  (Result (Univ _), Result Zero) -> Result (sub e a x m)
  (Result _, Result Zero)        -> Error TypeMismatch (Just (show m ++ " is not a term of a universe"))
  (Result _, Result _)           -> Error TypeMismatch (Just (show a ++ " is not of the type " ++ show Zero))
  (Error errc s, _)              -> Error errc s
  (_, Error errc s)              -> Error errc s
inferType e g (Ind One (NoBind m) [NoBind c] a)                                         = inferType e g (Ind One (Bind (getFreshVar e m) (NoBind m)) [NoBind c] a)
inferType e g (Ind One (Bind x (NoBind m)) [NoBind c] a)                                = case (inferType e ((x, One) : g) m, inferType e g c, inferType e g a) of
  (Result (Univ _), Result t, Result One) -> if t === sub e Star x m $ g then Result (sub e a x m) else Error TypeMismatch (Just ("The term " ++ show c ++ " does not have the type of the motive " ++ show m))
  (Result _, Result t, Result One)        -> Error TypeMismatch (Just (show m ++ " is not a term of a universe"))
  (Result _, Result _, Result _)          -> Error TypeMismatch (Just (show a ++ " is not of the type " ++ show One))
  (Error errc s, _, _)                    -> Error errc s
  (_, Error errc s, _)                    -> Error errc s
  (_, _, Error errc s)                    -> Error errc s
inferType e g (Ind (Sigma (x, t) n) (NoBind m) [Bind w (Bind y (NoBind f))] a)          = inferType e g (Ind (Sigma (x, t) n) (Bind (getFreshVar e m) (NoBind m)) [Bind w (Bind y (NoBind f))] a)
inferType e g (Ind (Sigma (x, t) n) (Bind z (NoBind m)) [Bind w (Bind y (NoBind f))] a) = case (inferType e ((z, Sigma (x, t) n) : g) m, inferType e ((w, t) : (y, n) : g) f, inferType e g a) of
  (Result (Univ _), Result s, Result s') -> case (s === sub e (Pair (Var w) (Var y)) z m $ e , s' === Sigma (x, t) n $ e) of
    (True, True) -> Result (sub e a z m)
    (True, _)    -> Error TypeMismatch (Just ("The term " ++ show s' ++ " is not of the type " ++ show (Sigma (x, t) n)))
    (_, _)       -> Error TypeMismatch (Just ("The term " ++ show s ++ " is not of the type " ++ show (sub e (Pair (Var w) (Var y)) z m)))
  (Result _, Result _, Result _)         -> Error TypeMismatch (Just (show m ++ " is not a term of a universe"))
  (Error errc s, _, _)                   -> Error errc s
  (_, Error errc s, _)                   -> Error errc s
  (_, _, Error errc s)                   -> Error errc s
inferType e g (Ind t m c a)                                                             = Error FailedToInferType (Just ("Invalid induction " ++ show (Ind t m c a)))

-- TODO: Use expected type to type sigma terms
checkType :: Environment -> Context -> Term -> Term -> CanError Term
checkType e g m t = checkTypeWithContexts e g m g t
  where
    checkInferredTypeMatch :: Environment -> Context -> Term -> Term -> CanError Term
    checkInferredTypeMatch e g m t = case inferType e g m of
      Result t'    -> if t === t' $ e then Result t else Error TypeMismatch (Just ("The type of " ++ show m ++ " is " ++ show (unsafeEval e t') ++ " but expected " ++ show (unsafeEval e t)))
      Error errc s -> Error errc s

    checkTypeWithContexts :: Environment -> Context -> Term -> Context -> Term -> CanError Term
    checkTypeWithContexts e g (Lam (Exp (x, t)) m) g' (Pi (x', t') n) = case (inferType e g t, inferType e g' t', checkTypeWithContexts e ((x, t) : g) m ((x', t') : g') n) of
      (Result (Univ i), Result (Univ j), Result t') -> if i == j then Result (Pi (x, t) t') else Error TypeMismatch (Just ("The type of " ++ show t ++ " is " ++ show (Univ i) ++ " but expected " ++ show (Univ j)))
      (Result (Univ _), Result _, Result _)         -> Error TypeMismatch (Just (show t ++ " is not a term of a universe"))
      (Result _, Result (Univ _), Result _)         -> Error TypeMismatch (Just (show t' ++ " is not a term of a universe"))
      (Error errc s, _, _)                          -> Error errc s
      (_, Error errc s, _)                          -> Error errc s
      (_, _, Error errc s)                          -> Error errc s
    checkTypeWithContexts e g (Lam (Imp x) m) g' (Pi (x', t) n)       = case (inferType e g' t, checkTypeWithContexts e ((x, t) : g) m ((x, t) : g') (sub e (Var x) x' n)) of
      (Result (Univ _), Result t') -> Result (Pi (x', t) t')
      (_, Result _)                -> Error TypeMismatch (Just (show t ++ " is not a term of a universe"))
      (Error errc s, _)            -> Error errc s
      (_, Error errc s)            -> Error errc s
    checkTypeWithContexts e g (Pair m n) g' (Sigma (x, t) t')         = case (inferType e g' t, inferType e ((x, t) : g') t', checkTypeWithContexts e g m g' t, checkTypeWithContexts e g n g' t') of
      (Result (Univ _), Result (Univ _), Result a, Result b) -> if (a === t $ e) && (b === sub e m x t' $ e) then Result (Sigma (x, t) t') else Error TypeMismatch (Just (show t ++ " is not a term of a universe"))
      (Error errc s, _, _, _)                                -> Error errc s
      (_, Error errc s, _, _)                                -> Error errc s
      (_, _, Error errc s, _)                                -> Error errc s
      (_, _, _, Error errc s)                                -> Error errc s
    checkTypeWithContexts e g m _ t                                   = checkInferredTypeMatch e g m t

-- A is a type <=> A : Univ i, for some i
isType :: Environment -> Context -> Term -> Bool
isType e g a = case inferType e g a of
  Result (Univ _) -> True
  Result (Var x)  -> case lookup x e of
    Just m  -> isType e g m
    Nothing -> False
  _               -> False

ctx :: Environment -> Context -> Bool
ctx e []         = True
ctx e ((_, t):g) = isType e g t && ctx e g

isValue :: Environment -> Term -> Bool
isValue e (Lam _ _) = True
isValue e (Var x)   = case lookup x e of
    Just m  -> isValue e m
    Nothing -> True
isValue e m         = isNeutral e m

isNeutral :: Environment -> Term -> Bool
isNeutral e (Var x)   = case lookup x e of
    Just m  -> isNeutral e m
    Nothing -> True
isNeutral e (App m n) = isNeutral e m && isValue e n
isNeutral e Star      = True
isNeutral e (Univ _)  = True
isNeutral e Zero      = True
isNeutral e One       = True
isNeutral e _         = False

isFreeIn :: ByteString -> Term -> Environment -> Bool
isFreeIn x (Var y) e        = case lookup y e of
  Just m  -> x `isFreeIn` m $ e
  Nothing -> x == y
isFreeIn x (App m n) e      = (x `isFreeIn` m $ e) || (x `isFreeIn` n $ e)
isFreeIn x (Lam (Exp (y, t)) m) e
  | x == y    = False
  | otherwise = (x `isFreeIn` m $ e) || (x `isFreeIn` t $ e)
isFreeIn x (Lam (Imp y) m) e
  | x == y    = False
  | otherwise = x `isFreeIn` m $ e
isFreeIn x (Pi (y, t) m) e
  | x == y    = False
  | otherwise = (x `isFreeIn` m $ e) || (x `isFreeIn` t $ e)
isFreeIn x (Sigma (y, t) m) e
  | x == y    = False
  | otherwise = (x `isFreeIn` m $ e) || (x `isFreeIn` t $ e)
isFreeIn x (Ind t' m c a) e = (x `isFreeIn` t' $ e) || (x `isFreeInBound` m $ e) || any (\c -> isFreeInBound x c e) c || (x `isFreeIn` a $ e)
isFreeIn x m              e = False

isFreeInBound :: ByteString -> BoundTerm -> Environment -> Bool
isFreeInBound x (Bind y t) e = (x /= y) && (x `isFreeInBound` t $ e)
isFreeInBound x (NoBind t) e = x `isFreeIn` t $ e

-- TODO: Make fresh var readable
getFreshVar :: Environment -> Term -> ByteString
getFreshVar e m = buildFreshVar e m (pack "a")
  where
    buildFreshVar :: Environment -> Term -> ByteString -> ByteString
    buildFreshVar e (Var y) x              = case lookup y e of
      Just m  -> buildFreshVar e m x
      Nothing -> x <> y
    buildFreshVar e (App m n) x            = buildFreshVar e m x <> buildFreshVar e n x
    buildFreshVar e (Lam (Exp (y, t)) m) x = buildFreshVar e m (x <> y) <> buildFreshVar e t x
    buildFreshVar e (Lam (Imp y) m) x      = buildFreshVar e m (x <> y)
    buildFreshVar e (Pi (y, t) m) x        = buildFreshVar e m (x <> y) <> buildFreshVar e t x
    buildFreshVar e (Sigma (y, t) m) x     = buildFreshVar e m (x <> y) <> buildFreshVar e t x
    buildFreshVar e (Ind t' m c a) x       = buildFreshVar e t' x <> buildFreshVarInBound e m x <> foldl (<>) (pack "") (map (\c -> buildFreshVarInBound e c x) c) <> buildFreshVar e a x
    buildFreshVar e m x                    = x

    buildFreshVarInBound :: Environment -> BoundTerm -> ByteString -> ByteString
    buildFreshVarInBound e (NoBind m) x = buildFreshVar e m x
    buildFreshVarInBound e (Bind y m) x = buildFreshVarInBound e m (x <> y)

sub :: Environment -> Term -> ByteString -> Term -> Term
sub e t x (Var y) = case lookup y e of
  Just m  -> sub e t x m
  Nothing -> if x == y then t else Var y
sub e t x (App m n)      = App (sub e t x m) (sub e t x n)
sub e t x (Lam (Exp (y, t')) m)
  | x == y             = Lam (Exp (y, sub e t x t')) m
  | y `isFreeIn` t $ e = Lam (Exp (freshVar, sub e t x t')) (sub e t x (sub e (Var freshVar) y m))
  | otherwise          = Lam (Exp (y, sub e t x t')) (sub e t x m)
  where
    freshVar :: ByteString
    freshVar = getFreshVar e m
sub e t x (Lam (Imp y) m)
  | x == y         = Lam (Imp y) m
  | y `isFreeIn` t $ e = Lam (Imp freshVar) (sub e t x (sub e (Var freshVar) y m))
  | otherwise      = Lam (Imp y) (sub e t x m)
  where
    freshVar :: ByteString
    freshVar = getFreshVar e m
sub e t x (Pi (y, t') m)
  | x == y             = Pi (y, t') m
  | y `isFreeIn` t $ e = Pi (freshVar, sub e t x t') (sub e t x (sub e (Var freshVar) y m))
  | otherwise          = Pi (y, sub e t x t') (sub e t x m)
  where
    freshVar :: ByteString
    freshVar = getFreshVar e m
sub e t x (Sigma (y, t') m)
  | x == y             = Sigma (y, t') m
  | y `isFreeIn` t $ e = Sigma (freshVar, sub e t x t') (sub e t x (sub e (Var freshVar) y m))
  | otherwise          = Sigma (y, sub e t x t') (sub e t x m)
  where
    freshVar :: ByteString
    freshVar = getFreshVar e m
sub e t x (Pair m n)     = Pair (sub e t x m) (sub e t x n)
sub e t x (Ind t' m c a) = Ind (sub e t x t') (subInBoundTerm e t x m) (map (subInBoundTerm e t x) c) (sub e t x a)
sub e t x m              = m

subInBoundTerm :: Environment -> Term -> ByteString -> BoundTerm -> BoundTerm
subInBoundTerm e t x (NoBind m) = NoBind (sub e t x m)
subInBoundTerm e t x (Bind y m)
  | x == y             = Bind y m
  | y `isFreeIn` t $ e = Bind freshVar (subInBoundTerm e t x (subInBoundTerm e (Var freshVar) y m))
  | otherwise          = Bind y (subInBoundTerm e t x m)
  where
    freshVar :: ByteString
    freshVar = getFreshVar e t

beta :: Environment -> Term -> Term
beta e (App (Lam (Exp (x, _)) m) n) = sub e n x m
beta e (App (Lam (Imp x) m) n)      = sub e n x m
beta e (Var x)                      = case lookup x e of
  Just m  -> beta e m
  Nothing -> Var x
beta e m                            = m

eval :: Environment -> Context -> Term -> CanError Term
eval e g m = case inferType e g m of
  Result t     -> Result (unsafeEval e t)
  Error errc s -> Error errc s

unsafeEval :: Environment -> Term -> Term
unsafeEval e (Var x)                                                     = case lookup x e of
  Just m  -> unsafeEval e m
  Nothing -> Var x
unsafeEval e (Lam (Exp (x, t)) (App f (Var x')))
  | x == x'   = unsafeEval e f -- Eta conversion
  | otherwise = Lam (Exp (x, unsafeEval e t)) (unsafeEval e (App f (Var x')))
unsafeEval e (Lam (Imp x) (App f (Var x')))
  | x == x'   = unsafeEval e f -- Eta conversion
  | otherwise = Lam (Imp x) (unsafeEval e (App f (Var x')))
unsafeEval e (Lam (Exp (x, t)) m)                                        = Lam (Exp (x, unsafeEval e t)) (unsafeEval e m)
unsafeEval e (Lam (Imp x) m)                                             = Lam (Imp x) (unsafeEval e m)
unsafeEval e (Pi (x, t) m)                                               = Pi (x, unsafeEval e t) (unsafeEval e m)
unsafeEval e (Sigma (x, t) m)                                            = Sigma (x, unsafeEval e t) (unsafeEval e m)
unsafeEval e (App m n)
  | isNeutral e f = App f (unsafeEval e n)
  | otherwise   = unsafeEval e (beta e (App f n))
  where
    f :: Term
    f = unsafeEval e m
unsafeEval e (Ind One _ [NoBind c] _)                                    = c
unsafeEval e (Ind (Sigma _ _) _ [Bind w (Bind y (NoBind f))] (Pair a b)) = sub e a w (sub e b y f)
unsafeEval e m                                                           = m

-- Judgemental equality of terms/types is alpha-beta-eta equivalence
instance JudgementalEq Term where
  (===) m n e = isAlphaEquiv e (unsafeEval e m) (unsafeEval e n)

instance JudgementalEq BoundTerm where
  (===) m n e = isAlphaEquivInBound e (unsafeEvalBoundTerm m) (unsafeEvalBoundTerm n)
    where
      unsafeEvalBoundTerm :: BoundTerm -> BoundTerm
      unsafeEvalBoundTerm (NoBind m) = NoBind (unsafeEval [] m)
      unsafeEvalBoundTerm (Bind a m) = Bind a (unsafeEvalBoundTerm m)

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
  show (Lam (Exp (x, t)) m)             = "\\(" ++ unpack x ++ " : " ++ show t ++ "). " ++ show m
  show (Lam (Imp x) m)                  = "\\" ++ unpack x ++ ". " ++ show m
  show (Univ 0)                         = "U"
  show (Univ i)                         = "U" ++ show i
  show Zero                             = "0"
  show One                              = "1"
  show (Pi (x, Pi (y, t') m) n)
    | x `isFreeIn` n $ []               = "(" ++ unpack x ++ " : " ++ show (Pi (y, t') m) ++ ") -> " ++ show n
    | otherwise                         = "(" ++ show (Pi (y, t') m) ++ ") -> " ++ show n
  show (Pi (x, t) m)
    | x `isFreeIn` m $ []                    = "(" ++ unpack x ++ " : " ++ show t ++ ") -> " ++ show m
    | otherwise                         = show t ++ " -> " ++ show m
  show (Sigma (x, t) (Sigma (y, t') m))
    | x `isFreeIn` Sigma (y, t') m $ [] = "(" ++ unpack x ++ " : " ++ show t ++ ") x " ++ "(" ++ show (Sigma (y, t') m) ++ ")"
    | otherwise                         = showSigmaOperarands t ++ " x (" ++ show (Sigma (y, t') m) ++ show ")"
  show (Sigma (x, t) m)
    | x `isFreeIn` m $ []               = "(" ++ unpack x ++ " : " ++ show t ++ ") x " ++ showSigmaOperarands m
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
