module Core.Judgement.Typing.Inference where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation
import Core.Judgement.Typing.Context

import Data.Maybe (fromMaybe)
import Control.Monad (unless)
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.ByteString.Lazy.Char8 (ByteString)

runInferType :: Term -> TypeCheck (Term, Term)
runInferType (Univ i)                                  = return (Univ i, Univ (i + 1))
runInferType Star                                      = return (Star, Top)
runInferType Bot                                       = return (Bot, Univ 0)
runInferType Top                                       = return (Top, Univ 0)
runInferType Nat                                       = return (Nat, Univ 0)

runInferType (Var (Bound i))                           = do
  ctxs <- ask

  if i >= 0 && i < length (bctx ctxs)
  then return (Var $ Bound i, snd $ bctx ctxs !! i)
  else typeError FailedToInferType $ Just ("Invalid index " ++ show i ++ " for bound term")

runInferType (Var (Free x))                            = do
  ctxs <- ask

  case lookup x $ ctx ctxs of
    Just t  -> return (Var $ Free x, t)
    Nothing -> typeError FailedToInferType $ Just ("Unknown variable " ++ show x)

runInferType (Var (Meta i sp))                         = do
  st <- get

  case lookup i $ mctx st of
    Just d  -> return (Var $ Meta i sp, mtype d)
    Nothing -> typeError FailedToInferType $ Just ("Unknown meta variable " ++ show (Var $ Meta i sp))

runInferType (Pi (x, t, ex) m)                         = do
  ctxs <- ask

  (et, tt) <- runInferEvaluatedType t
  (em, mt) <- local (addToBoundCtx (x, et)) (runInferEvaluatedType m)

  case (tt, mt) of
    (Univ i, Univ j) -> return (Pi (x, et, ex) em, Univ $ max i j)
    (Univ i, _)      -> typeError TypeMismatch $ Just (showTermWithContext ((x, t) : bctx ctxs) em ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) et ++ " is not a term of a universe")

runInferType (Sigma (x, t) m)                          = do
  ctxs <- ask

  (et, tt) <- runInferEvaluatedType t
  (em, mt) <- local (addToBoundCtx (x, et)) (runInferEvaluatedType m)

  case (tt, mt) of
    (Univ i, Univ j) -> return (Sigma (x, et) em, Univ $ max i j)
    (Univ i, _)      -> typeError TypeMismatch $ Just (showTermWithContext ((x, t) : bctx ctxs) em ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) et ++ " is not a term of a universe")

runInferType (Lam (x, Just t, ex) m)                   = do
  ctxs <- ask

  (et, tt) <- runInferEvaluatedType t
  (em, mt) <- local (addToBoundCtx (Just x, et)) (runInferTypeAndElab m)

  case tt of
    Univ i -> return (Lam (x, Just et, ex) em, Pi (if isBinderUsed mt then Just x else Nothing, et, ex) mt)
    _      -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) et ++ " is not a term of a universe")

runInferType (Lam (x, Nothing, ex) m)                  = do
  ctxs <- ask

  typeError FailedToInferType $ Just ("Cannot infer type of implicit lambda " ++ showTermWithContext (bctx ctxs) (Lam (x, Nothing, ex) m))

runInferType (App m (n, ex))                           = do
  ctxs <- ask
  -- Don't elaborate returned type, as inferAppType deals with implicit/explicit params
  (em, mt) <- runInferType m
  inferAppType em (n, ex) $ eval $ resolve (env ctxs) mt
    where
      inferAppType :: Term -> (Term, Explicitness) -> Term -> TypeCheck (Term, Term)
      inferAppType m (n, ex') mt = do
        ctxs <- ask

        case mt of
          Pi (x, t, Exp) t' -> do
            (en, nt) <- runInferTypeAndElab n

            unify t nt $ Just (showTermWithContext (bctx ctxs) m ++ " of type " ++ showTermWithContext (bctx ctxs) mt ++ " cannot be applied to " ++ showTermWithContext (bctx ctxs) en ++ " of type " ++ showTermWithContext (bctx ctxs) nt)
            return (App m (en, ex'), bumpDown $ open (bumpUp en) t')
          Pi (x, t, Imp) t' -> do
            if ex == Imp
            then do
              -- If user supplies implicit variable explicitely, simply infer type using
              -- explicit type and term as normal
              (_, at) <- inferAppType m (n, Exp) $ Pi (x, t, Exp) t'
              return (App m (n, Imp), at)
            else do
              -- Otherwise, create a meta variable and continue with type inference
              mv <- createMetaVar t $ bctx ctxs
              let m'  = App m (mv, Imp)
              let m't = bumpDown $ open (bumpUp mv) t'

              inferAppType m' (n, ex) m't
          _                 -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) m ++ " is not a term of a Pi type")

runInferType (Pair m n)                                = do
  (em, mt) <- runInferTypeAndElab m
  (en, nt) <- runInferTypeAndElab n

  return (Pair em en, Sigma (Nothing, mt) $ bumpUp nt)

runInferType (Sum m n)                                 = do
  ctxs <- ask

  (em, mt) <- runInferEvaluatedType m
  (en, nt) <- runInferEvaluatedType n

  case (mt, nt) of
    (Univ i, Univ j) -> return (Sum em en, Univ $ max i j)
    (Univ i, _)      -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) en ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (show em ++ " is not a term of a universe")

runInferType (Inl m)                                   = do
  ctxs <- ask

  typeError FailedToInferType $ Just ("Cannot infer type of ambiguous injection " ++ showTermWithContext (bctx ctxs) (Inl m))

runInferType (Inr m)                                   = do
  ctxs <- ask

  typeError FailedToInferType $ Just ("Cannot infer type of ambiguous injection " ++ showTermWithContext (bctx ctxs) (Inr m))

runInferType Zero                                      = return (Zero, Nat)

runInferType (Succ m)                                  = do
  ctxs <- ask

  (em, mt) <- runInferEvaluatedType m

  unify mt Nat $ Just ("Cannot apply succ to a term of type " ++ showTermWithContext (bctx ctxs) mt)
  return (Succ em, Nat)

runInferType (Funext p)                                = do
  ctxs <- ask

  (ep, pt) <- runInferTypeAndElab p

  case resolve (env ctxs) pt of
    Pi _ (Id _ (App f (Var (Bound 0), Exp)) (App g (Var (Bound 0), Exp))) -> do
      runInferType pt
      return (Funext ep, Id Nothing f g)
    _                                                                     -> typeError FailedToInferType $ Just ("Cannot apply funext to a term of type " ++ showTermWithContext (bctx ctxs) pt)

-- TODO: Type check univalence
runInferType (Univalence f)                            = do
  ctxs <- ask

  (ef, ft) <- runInferEvaluatedType f

  case ft of
    Top -> return (Univalence ef, Top)
    _   -> typeError FailedToInferType $ Just ("Cannot apply univalence to a term of type " ++ showTermWithContext (bctx ctxs) ft)

runInferType (IdFam t)                                 = do
  ctxs <- ask

  (et, tt) <- runInferTypeAndElab t

  case eval $ resolve (env ctxs) tt of
    Univ i -> return (IdFam et, Pi (Nothing, et, Exp) $ Pi (Nothing, et, Exp) tt)
    _      -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) et ++ " is not a term of a universe")

runInferType (Id Nothing m n)                          = do
  (em, mt)   <- runInferTypeAndElab m
  (emt, mtt) <- runInferTypeAndElab mt
  (en, nt)   <- runCheckEvaluatedType n mt

  return (Id Nothing em en, mtt)

runInferType (Id (Just t) m n)                         = do
  (et, tt) <- runInferTypeAndElab t
  (em, mt) <- runCheckEvaluatedType m t
  (en, nt) <- runCheckEvaluatedType n t

  return (Id (Just et) em en, tt)

runInferType (Refl m)                                  = do
  (em, mt) <- runInferTypeAndElab m

  return (Refl em, Id Nothing em em)

runInferType (Ind Bot (NoBind m) [] a)                 = runInferType (Ind Bot (Bind Nothing $ NoBind $ bumpUp m) [] a)

runInferType (Ind Bot (Bind x (NoBind m)) [] a)        = do
  ctxs <- ask

  (em, mt) <- local (addToBoundCtx (x, Bot)) (runInferEvaluatedType m)
  (ea, at) <- runCheckType a Bot

  case mt of
    Univ _ -> return (Ind Bot (Bind x (NoBind em)) [] ea, bumpDown $ open (bumpUp ea) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((x, Bot) : bctx ctxs) em ++ " is not a term of a universe")

runInferType (Ind Top (NoBind m) [NoBind c] a)          = runInferType (Ind Top (Bind Nothing $ NoBind $ bumpUp m) [NoBind c] a)

runInferType (Ind Top (Bind x (NoBind m)) [NoBind c] a) = do
  ctxs <- ask

  (em, mt) <- local (addToBoundCtx (x, Top)) (runInferEvaluatedType m)
  (ec, ct) <- local useBoundCtx $ runCheckEvaluatedType c (bumpDown $ open Star em)
  (ea, at) <- runCheckType a Top

  case mt of
    Univ _ -> return (Ind Top (Bind x (NoBind em)) [NoBind ec] ea, bumpDown $ open (bumpUp ea) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((x, Top) : bctx ctxs) em ++ " is not a term of a universe")

runInferType (Ind
  (Sigma (x, t) n)
  (NoBind m)
  [Bind w (Bind y (NoBind f))]
  a)                                                    = runInferType (Ind (Sigma (x, t) n) (Bind Nothing $ NoBind $ bumpUp m) [Bind w $ Bind y $ NoBind f] a)

runInferType (Ind
  (Sigma (x, t) n)
  (Bind z (NoBind m))
  [Bind w (Bind y (NoBind f))]
  a)                                                    = do
  ctxs <- ask

  (em, mt) <- local (addToBoundCtx (z, Sigma (x, t) n)) (runInferEvaluatedType m)
  (ef, ft) <- local (useBoundCtx . addToBoundCtx (y, n) . addToBoundCtx (w, t)) (runCheckEvaluatedType f $ openFor (Pair (Var $ Bound 1) (Var $ Bound 0)) 1 (bumpUp em))
  (ea, at) <- runCheckEvaluatedType a (Sigma (x, t) n)

  case mt of
    Univ _ -> return (Ind
      (Sigma (x, t) n)
      (Bind z (NoBind em))
      [Bind w (Bind y (NoBind ef))]
      ea, bumpDown $ open (bumpUp ea) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((z, Sigma (x, t) n) : bctx ctxs) em ++ " is not a term of a universe")

runInferType (Ind
  (Sum t n)
  (NoBind m)
  [Bind x (NoBind c), Bind y (NoBind d)]
  a)                                                    = runInferType (Ind (Sum t n) (Bind Nothing $ NoBind $ bumpUp m) [Bind x $ NoBind c, Bind y $ NoBind d] a)

runInferType (Ind
  (Sum t n)
  (Bind z (NoBind m))
  [Bind x (NoBind c), Bind y (NoBind d)]
  a)                                                    = do
  ctxs <- ask

  (em, mt) <- local (addToBoundCtx (z, Sum t n)) (runInferEvaluatedType m)
  (ec, ct) <- local (useBoundCtx . addToBoundCtx (x, t)) (runCheckEvaluatedType c $ open (Inl $ Var $ Bound 1) em)
  (ed, dt) <- local (useBoundCtx . addToBoundCtx (y, n)) (runCheckEvaluatedType d $ open (Inr $ Var $ Bound 1) em)
  (ea, at) <- runCheckEvaluatedType a (Sum t n)

  case mt of
    Univ _ -> return (Ind
      (Sum t n)
      (Bind z (NoBind em))
      [Bind x (NoBind ec), Bind y (NoBind ed)]
      ea, bumpDown $ open (bumpUp ea) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((z, Sum t n) : bctx ctxs) em ++ " is not a term of a universe")

runInferType (Ind
  (IdFam t)
  (NoBind m)
  [Bind z (NoBind c), NoBind a, NoBind b]
  p)                                                    = runInferType (Ind (IdFam t) (Bind Nothing $ Bind Nothing $ Bind Nothing $ NoBind $ shift 3 m) [Bind z $ NoBind c, NoBind a, NoBind b] p)

runInferType (Ind
  (IdFam t)
  (NoBind m)
  [Bind z (NoBind c), NoBind a, NoBind b]
  p)                                                    = runInferType (Ind (IdFam t) (Bind Nothing $ Bind Nothing $ Bind Nothing $ NoBind $ shift 3 m) [Bind z $ NoBind c, NoBind a, NoBind b] p)

runInferType (Ind
  (IdFam t)
  (Bind x (Bind y (Bind p (NoBind m))))
  [Bind z (NoBind c), NoBind a, NoBind b]
  p')                                                   = do
  ctxs <- ask

  (ea, at) <- runCheckEvaluatedType a t
  (eb, bt) <- runCheckEvaluatedType b t

  (em, mt)   <- local (addToBoundCtx (p, Id (Just $ shift 2 t) (Var $ Bound 2) (Var $ Bound 1)) . addToBoundCtx (y, bumpUp t) . addToBoundCtx (x, t)) (runInferEvaluatedType m)
  (ec, ct)   <- local (useBoundCtx . addToBoundCtx (z, t)) (runCheckEvaluatedType c $ shift (-2) $ openFor (Var $ Bound 2) 2 $ openFor (Var $ Bound 2) 1 $ open (Refl $ Var $ Bound 2) em)
  (ep', p't) <- local useBoundCtx $ runCheckEvaluatedType p' (Id (Just t) ea eb)

  case mt of
    Univ _ -> return (Ind
      (IdFam t)
      (Bind x (Bind y (Bind p (NoBind em))))
      [Bind z (NoBind ec), NoBind ea, NoBind eb]
      ep', shift (-3) $ openFor (shift 3 ea) 2 $ openFor (shift 3 eb) 1 $ open (shift 3 ep') em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((p, Id (Just $ shift 2 t) (Var $ Bound 2) (Var $ Bound 1)) : (y, bumpUp t) : (x, t) : bctx ctxs) em ++ " is not a term of a universe")

runInferType (Ind (Var (Free x)) m c a)                 = do
  ctxs <- ask

  case lookup x $ env ctxs of
    Just t  -> runInferType $ Ind t m c a
    Nothing -> typeError FailedToInferType $ Just ("Unknown variable " ++ show x)

runInferType (Ind
  Nat
  (NoBind m)
  [NoBind c0, Bind w (Bind z (NoBind cs))]
  n)                                                    = runInferType (Ind Nat (Bind Nothing $ NoBind $ bumpUp m) [NoBind c0, Bind w (Bind z (NoBind cs))] n)

runInferType (Ind
  Nat
  (Bind x (NoBind m))
  [NoBind c0, Bind w (Bind z (NoBind cs))]
  n)                                                    = do
  ctxs <- ask

  (en, nt)   <- runCheckType n Nat
  (em, mt)   <- local (addToBoundCtx (x, Nat)) (runInferEvaluatedType m)
  (ec0, c0t) <- local useBoundCtx $ runCheckEvaluatedType c0 $ bumpDown $ open Zero em
  (ecs, cst) <- local (useBoundCtx . addToBoundCtx (z, em) . addToBoundCtx (w, Nat)) (runCheckEvaluatedType cs $ bumpUp $ open (Succ $ Var $ Bound 0) em)

  case mt of
    Univ _ -> return (Ind
      Nat
      (Bind x (NoBind em))
      [NoBind ec0, Bind w (Bind z (NoBind ecs))]
      en, bumpDown $ open (bumpUp en) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((x, Nat) : bctx ctxs) em ++ " is not a term of a universe")

runInferType (Ind t m c a)                              = typeError FailedToInferType $ Just ("Invalid induction " ++ show (Ind t m c a))

runCheckType :: Term -> Term -> TypeCheck (Term, Term)
runCheckType m (Var (Free x))                             = do
  ctxs <- ask

  case lookup x $ env ctxs of
    Just t  -> do
      (em, _) <- runCheckType m t
      return (em, Var $ Free x)
    Nothing -> unifyInferredType m (Var $ Free x)

runCheckType (Lam (x, Just t, ex) m) (Pi (x', t', ex') n) = do
  ctxs <- ask

  (et, tt)   <- runInferEvaluatedType t
  (et', t't) <- local useTypeBoundCtx (runInferEvaluatedType t')
  (em, mt)   <- local (addToBoundCtxs (Just x, et) (x', et')) (runCheckType m n)

  case (tt, t't, ex == ex') of
    (_, _, False)       -> typeError TypeMismatch $ Just ("Mismatching explicitness between " ++ showTermWithContext (bctx ctxs) (Lam (x, Just et, ex) em) ++ " and " ++ showTermWithContext (tbctx ctxs) (Pi (x', et, ex') n))
    (Univ i, Univ j, _) -> do
      unify et et' Nothing
      return (Lam (x, Just et, ex) em, Pi (x', et, Exp) mt)
    (Univ _, _, _)      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et' ++ " is not a term of a universe")
    (_, _, _)           -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) et ++ " is not a term of a universe")

runCheckType (Lam (x, Nothing, ex) m) (Pi (x', t, ex') n) = do
  ctxs <- ask

  (et, tt) <- local useTypeBoundCtx (runInferEvaluatedType t)
  (em, mt) <- local (addToBoundCtxs (Just x, et) (x', et)) (runCheckType m n)

  case tt of
    Univ _ -> if ex == ex'
      then return (Lam (x, Nothing, ex) em, Pi (x', et, Exp) mt)
      else typeError TypeMismatch $ Just ("Mismatching explicitness between " ++ showTermWithContext (bctx ctxs) (Lam (x, Nothing, ex) em) ++ " and " ++ showTermWithContext (tbctx ctxs) (Pi (x', et, ex') n))
    _      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et ++ " is not a term of a universe")

runCheckType (Pair m n) (Sigma (x, t) t')                 = do
  ctxs <- ask

  (et, tt)   <- runInferEvaluatedType t
  (et', t't) <- local (addToBoundCtx (x, et) . useTypeBoundCtx) (runInferEvaluatedType t')
  (em, mt)   <- runCheckType m et
  (en, nt)   <- runCheckType n (bumpDown $ open (bumpUp em) et')

  case (tt, t't) of
    (Univ _, Univ _) -> return (Pair em en, Sigma (x, et) et')
    (Univ _, _)      -> typeError TypeMismatch $ Just (showTermWithContext ((x, et) : tbctx ctxs) et' ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et ++ " is not a term of a universe")

runCheckType (Inl m) (Sum t t')                           = do
  ctxs <- ask

  (em, mt)   <- runCheckType m t
  (et, tt)   <- local useTypeBoundCtx (runInferEvaluatedType t)
  (et', t't) <- local useTypeBoundCtx (runInferEvaluatedType t')

  case (tt, t't) of
    (Univ _, Univ _) -> return (Inl em, Sum et et')
    (Univ _, _)      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et' ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et ++ " is not a term of a universe")

runCheckType (Inr m) (Sum t t')                           = do
  ctxs <- ask

  (em, mt)   <- runCheckType m t'
  (et, tt)   <- local useTypeBoundCtx (runInferEvaluatedType t)
  (et', t't) <- local useTypeBoundCtx (runInferEvaluatedType t')

  case (tt, t't) of
    (Univ _, Univ _) -> return (Inr em, Sum et et')
    (Univ _, _)      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et' ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et ++ " is not a term of a universe")

runCheckType m t                                          = unifyInferredType m t

unifyInferredType :: Term -> Term -> TypeCheck (Term, Term)
unifyInferredType m t = do
  ctxs <- ask

  (em, mt) <- runInferTypeAndElab m
  unify mt t $ Just ("The type of " ++ showTermWithContext (bctx ctxs) em ++ " is " ++ showTermWithContext (bctx ctxs) (eval mt) ++ " but expected " ++ showTermWithContext (tbctx ctxs) t)
  return (em, t)

runInferEvaluatedType :: Term -> TypeCheck (Term, Term)
runInferEvaluatedType m = do
  ctxs <- ask

  (em, mt) <- runInferTypeAndElab m
  return (em, eval $ resolve (env ctxs) mt)

runCheckEvaluatedType :: Term -> Term -> TypeCheck (Term, Term)
runCheckEvaluatedType m t = do
  ctxs <- ask

  runCheckType m (eval $ resolve (env ctxs) t)

instantiateImplicits :: Term -> Term -> TypeCheck (Term, Term)
instantiateImplicits em (Pi (x, t, Imp) t') = do
  ctxs <- ask

  mv <- createMetaVar t $ bctx ctxs
  let em'  = App em (mv, Imp)
  let em't = bumpDown $ open (bumpUp mv) t'
  instantiateImplicits em' em't
instantiateImplicits em mt                  = return (em, mt)

runInferTypeAndElab :: Term -> TypeCheck (Term, Term)
runInferTypeAndElab m = do
  (em, mt) <- runInferType m
  instantiateImplicits em mt

unify :: Term -> Term -> Maybe String -> TypeCheck ()
unify t t' ms = do
  ctxs <- ask
  let errorString = fromMaybe ("Failed to unify types " ++ showTermWithContext (bctx ctxs) t ++ " and " ++ showTermWithContext (bctx ctxs) t') ms

  if containsMeta t || containsMeta t'
  then do
    -- Add constraint
    st <- get
    let cst = (bctx ctxs, t, t')
    put st { mcsts=cst : mcsts st }
  else do
    unless (equal (env ctxs) t t') $
      typeError TypeMismatch $ Just errorString
