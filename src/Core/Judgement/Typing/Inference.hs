module Core.Judgement.Typing.Inference (runInferType, evalInferType, runCheckType, evalCheckType) where

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

runInferType :: Contexts -> MetaState -> Term -> CanError ((Term, Term), MetaState)
runInferType ctxs st m = runStateT (runReaderT (goInferType m) ctxs) st

evalInferType :: Contexts -> MetaState -> Term -> CanError (Term, Term)
evalInferType ctxs st m = evalStateT (runReaderT (goInferType m) ctxs) st

goInferType :: Term -> TypeCheck (Term, Term)
goInferType (Univ i)                                  = return (Univ i, Univ (i + 1))
goInferType Star                                      = return (Star, Top)
goInferType Bot                                       = return (Bot, Univ 0)
goInferType Top                                       = return (Top, Univ 0)
goInferType Nat                                       = return (Nat, Univ 0)

goInferType (Var (Bound i))                           = do
  ctxs <- ask

  if i >= 0 && i < length (bctx ctxs)
  then return (Var $ Bound i, snd $ bctx ctxs !! i)
  else typeError FailedToInferType $ Just ("Invalid index " ++ show i ++ " for bound term")

goInferType (Var (Free x))                            = do
  ctxs <- ask

  case lookup x $ ctx ctxs of
    Just t  -> return (Var $ Free x, t)
    Nothing -> typeError FailedToInferType $ Just ("Unknown variable " ++ show x)

goInferType (Var (Meta i sp))                         = do
  st <- get

  case lookup i $ mctx st of
    Just d  -> return (Var $ Meta i sp, mtype d)
    Nothing -> typeError FailedToInferType $ Just ("Unknown meta variable " ++ show (Var $ Meta i sp))

goInferType (Pi (x, t, ex) m)                         = do
  ctxs <- ask

  (et, tt) <- goInferEvaluatedType t
  (em, mt) <- local (addToBoundCtx (x, et)) (goInferEvaluatedType m)

  case (tt, mt) of
    (Univ i, Univ j) -> return (Pi (x, et, ex) em, Univ $ max i j)
    (Univ i, _)      -> typeError TypeMismatch $ Just (showTermWithContext ((x, t) : bctx ctxs) em ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) et ++ " is not a term of a universe")

goInferType (Sigma (x, t) m)                          = do
  ctxs <- ask

  (et, tt) <- goInferEvaluatedType t
  (em, mt) <- local (addToBoundCtx (x, et)) (goInferEvaluatedType m)

  case (tt, mt) of
    (Univ i, Univ j) -> return (Sigma (x, et) em, Univ $ max i j)
    (Univ i, _)      -> typeError TypeMismatch $ Just (showTermWithContext ((x, t) : bctx ctxs) em ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) et ++ " is not a term of a universe")

goInferType (Lam (x, Just t, ex) m)                   = do
  ctxs <- ask

  (et, tt) <- goInferEvaluatedType t
  (em, mt) <- local (addToBoundCtx (Just x, et)) (goInferTypeAndElab m)

  case tt of
    Univ i -> return (Lam (x, Just et, ex) em, Pi (if isBinderUsed mt then Just x else Nothing, et, ex) mt)
    _      -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) et ++ " is not a term of a universe")

goInferType (Lam (x, Nothing, ex) m)                  = do
  ctxs <- ask

  typeError FailedToInferType $ Just ("Cannot infer type of implicit lambda " ++ showTermWithContext (bctx ctxs) (Lam (x, Nothing, ex) m))

goInferType (App m (n, ex))                           = do
  ctxs <- ask
  -- Don't elaborate returned type, as inferAppType deals with implicit/explicit params
  (em, mt) <- goInferType m
  inferAppType em (n, ex) $ eval $ resolve (env ctxs) mt
    where
      inferAppType :: Term -> (Term, Explicitness) -> Term -> TypeCheck (Term, Term)
      inferAppType m (n, ex') mt = do
        ctxs <- ask

        case mt of
          Pi (x, t, Exp) t' -> do
            (en, nt) <- goInferTypeAndElab n

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
          Var (Meta i sp)   -> do
            (_, nt) <- goInferTypeAndElab n
            (_, mit) <- goInferType $ Var $ Meta i sp
            (_, ntt) <- goInferType nt

            -- TODO: Implement Universe Polymorphism to avoid this erroring,
            -- allow user to abstract over universes, and allow metas in case
            -- statements matching universes
            mtype <- case (mit, ntt) of
              (Univ i, Univ j)    -> return $ Univ $ max i j
              (_, _)              -> typeError TypeMismatch $ Just ("Unable to resolve type of meta " ++ show (Var $ Meta i sp))
            mv <- createMetaVar mtype $ bctx ctxs

            -- Refine the meta to be a pi type
            let mmt = Pi (Nothing, nt, Exp) mv
            unify (Var $ Meta i sp) mmt Nothing

            inferAppType m (n, ex') mmt
          _                 -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) m ++ " is not a term of a Pi type")

goInferType (Pair m n)                                = do
  (em, mt) <- goInferTypeAndElab m
  (en, nt) <- goInferTypeAndElab n

  return (Pair em en, Sigma (Nothing, mt) $ bumpUp nt)

goInferType (Sum m n)                                 = do
  ctxs <- ask

  (em, mt) <- goInferEvaluatedType m
  (en, nt) <- goInferEvaluatedType n

  case (mt, nt) of
    (Univ i, Univ j) -> return (Sum em en, Univ $ max i j)
    (Univ i, _)      -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) en ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (show em ++ " is not a term of a universe")

goInferType (Inl m)                                   = do
  ctxs <- ask

  typeError FailedToInferType $ Just ("Cannot infer type of ambiguous injection " ++ showTermWithContext (bctx ctxs) (Inl m))

goInferType (Inr m)                                   = do
  ctxs <- ask

  typeError FailedToInferType $ Just ("Cannot infer type of ambiguous injection " ++ showTermWithContext (bctx ctxs) (Inr m))

goInferType Zero                                      = return (Zero, Nat)

goInferType (Succ m)                                  = do
  ctxs <- ask

  (em, mt) <- goInferEvaluatedType m

  unify mt Nat $ Just ("Cannot apply succ to a term of type " ++ showTermWithContext (bctx ctxs) mt)
  return (Succ em, Nat)

goInferType (Funext p)                                = do
  ctxs <- ask

  (ep, pt) <- goInferTypeAndElab p

  case resolve (env ctxs) pt of
    Pi _ (Id _ (App f (Var (Bound 0), Exp)) (App g (Var (Bound 0), Exp))) -> do
      goInferType pt
      return (Funext ep, Id Nothing f g)
    _                                                                     -> typeError FailedToInferType $ Just ("Cannot apply funext to a term of type " ++ showTermWithContext (bctx ctxs) pt)

-- TODO: Type check univalence
goInferType (Univalence f)                            = do
  ctxs <- ask

  (ef, ft) <- goInferEvaluatedType f

  case ft of
    Top -> return (Univalence ef, Top)
    _   -> typeError FailedToInferType $ Just ("Cannot apply univalence to a term of type " ++ showTermWithContext (bctx ctxs) ft)

goInferType (IdFam t)                                 = do
  ctxs <- ask

  (et, tt) <- goInferTypeAndElab t

  case eval $ resolve (env ctxs) tt of
    Univ i -> return (IdFam et, Pi (Nothing, et, Exp) $ Pi (Nothing, et, Exp) tt)
    _      -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) et ++ " is not a term of a universe")

goInferType (Id Nothing m n)                          = do
  (em, mt)   <- goInferTypeAndElab m
  (emt, mtt) <- goInferTypeAndElab mt
  (en, nt)   <- goCheckEvaluatedType n mt

  return (Id Nothing em en, mtt)

goInferType (Id (Just t) m n)                         = do
  (et, tt) <- goInferTypeAndElab t
  (em, mt) <- goCheckEvaluatedType m t
  (en, nt) <- goCheckEvaluatedType n t

  return (Id (Just et) em en, tt)

goInferType (Refl m)                                  = do
  (em, mt) <- goInferTypeAndElab m

  return (Refl em, Id Nothing em em)

goInferType (Ind Bot (NoBind m) [] a)                 = goInferType (Ind Bot (Bind Nothing $ NoBind $ bumpUp m) [] a)

goInferType (Ind Bot (Bind x (NoBind m)) [] a)        = do
  ctxs <- ask

  (em, mt) <- local (addToBoundCtx (x, Bot)) (goInferEvaluatedType m)
  (ea, at) <- goCheckType a Bot

  case mt of
    Univ _ -> return (Ind Bot (Bind x (NoBind em)) [] ea, bumpDown $ open (bumpUp ea) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((x, Bot) : bctx ctxs) em ++ " is not a term of a universe")

goInferType (Ind Top (NoBind m) [NoBind c] a)          = goInferType (Ind Top (Bind Nothing $ NoBind $ bumpUp m) [NoBind c] a)

goInferType (Ind Top (Bind x (NoBind m)) [NoBind c] a) = do
  ctxs <- ask

  (em, mt) <- local (addToBoundCtx (x, Top)) (goInferEvaluatedType m)
  (ec, ct) <- local useBoundCtx $ goCheckEvaluatedType c (bumpDown $ open Star em)
  (ea, at) <- goCheckType a Top

  case mt of
    Univ _ -> return (Ind Top (Bind x (NoBind em)) [NoBind ec] ea, bumpDown $ open (bumpUp ea) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((x, Top) : bctx ctxs) em ++ " is not a term of a universe")

goInferType (Ind
  (Sigma (x, t) n)
  (NoBind m)
  [Bind w (Bind y (NoBind f))]
  a)                                                    = goInferType (Ind (Sigma (x, t) n) (Bind Nothing $ NoBind $ bumpUp m) [Bind w $ Bind y $ NoBind f] a)

goInferType (Ind
  (Sigma (x, t) n)
  (Bind z (NoBind m))
  [Bind w (Bind y (NoBind f))]
  a)                                                    = do
  ctxs <- ask

  (em, mt) <- local (addToBoundCtx (z, Sigma (x, t) n)) (goInferEvaluatedType m)
  (ef, ft) <- local (useBoundCtx . addToBoundCtx (y, n) . addToBoundCtx (w, t)) (goCheckEvaluatedType f $ openFor (Pair (Var $ Bound 1) (Var $ Bound 0)) 1 (bumpUp em))
  (ea, at) <- goCheckEvaluatedType a (Sigma (x, t) n)

  case mt of
    Univ _ -> return (Ind
      (Sigma (x, t) n)
      (Bind z (NoBind em))
      [Bind w (Bind y (NoBind ef))]
      ea, bumpDown $ open (bumpUp ea) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((z, Sigma (x, t) n) : bctx ctxs) em ++ " is not a term of a universe")

goInferType (Ind
  (Sum t n)
  (NoBind m)
  [Bind x (NoBind c), Bind y (NoBind d)]
  a)                                                    = goInferType (Ind (Sum t n) (Bind Nothing $ NoBind $ bumpUp m) [Bind x $ NoBind c, Bind y $ NoBind d] a)

goInferType (Ind
  (Sum t n)
  (Bind z (NoBind m))
  [Bind x (NoBind c), Bind y (NoBind d)]
  a)                                                    = do
  ctxs <- ask

  (em, mt) <- local (addToBoundCtx (z, Sum t n)) (goInferEvaluatedType m)
  (ec, ct) <- local (useBoundCtx . addToBoundCtx (x, t)) (goCheckEvaluatedType c $ open (Inl $ Var $ Bound 1) em)
  (ed, dt) <- local (useBoundCtx . addToBoundCtx (y, n)) (goCheckEvaluatedType d $ open (Inr $ Var $ Bound 1) em)
  (ea, at) <- goCheckEvaluatedType a (Sum t n)

  case mt of
    Univ _ -> return (Ind
      (Sum t n)
      (Bind z (NoBind em))
      [Bind x (NoBind ec), Bind y (NoBind ed)]
      ea, bumpDown $ open (bumpUp ea) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((z, Sum t n) : bctx ctxs) em ++ " is not a term of a universe")

goInferType (Ind
  (IdFam t)
  (NoBind m)
  [Bind z (NoBind c), NoBind a, NoBind b]
  p)                                                    = goInferType (Ind (IdFam t) (Bind Nothing $ Bind Nothing $ Bind Nothing $ NoBind $ shift 3 m) [Bind z $ NoBind c, NoBind a, NoBind b] p)

goInferType (Ind
  (IdFam t)
  (NoBind m)
  [Bind z (NoBind c), NoBind a, NoBind b]
  p)                                                    = goInferType (Ind (IdFam t) (Bind Nothing $ Bind Nothing $ Bind Nothing $ NoBind $ shift 3 m) [Bind z $ NoBind c, NoBind a, NoBind b] p)

goInferType (Ind
  (IdFam t)
  (Bind x (Bind y (Bind p (NoBind m))))
  [Bind z (NoBind c), NoBind a, NoBind b]
  p')                                                   = do
  ctxs <- ask

  (ea, at) <- goCheckEvaluatedType a t
  (eb, bt) <- goCheckEvaluatedType b t

  (em, mt)   <- local (addToBoundCtx (p, Id (Just $ shift 2 t) (Var $ Bound 2) (Var $ Bound 1)) . addToBoundCtx (y, bumpUp t) . addToBoundCtx (x, t)) (goInferEvaluatedType m)
  (ec, ct)   <- local (useBoundCtx . addToBoundCtx (z, t)) (goCheckEvaluatedType c $ shift (-2) $ openFor (Var $ Bound 2) 2 $ openFor (Var $ Bound 2) 1 $ open (Refl $ Var $ Bound 2) em)
  (ep', p't) <- local useBoundCtx $ goCheckEvaluatedType p' (Id (Just t) ea eb)

  case mt of
    Univ _ -> return (Ind
      (IdFam t)
      (Bind x (Bind y (Bind p (NoBind em))))
      [Bind z (NoBind ec), NoBind ea, NoBind eb]
      ep', shift (-3) $ openFor (shift 3 ea) 2 $ openFor (shift 3 eb) 1 $ open (shift 3 ep') em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((p, Id (Just $ shift 2 t) (Var $ Bound 2) (Var $ Bound 1)) : (y, bumpUp t) : (x, t) : bctx ctxs) em ++ " is not a term of a universe")

goInferType (Ind (Var (Free x)) m c a)                 = do
  ctxs <- ask

  case lookup x $ env ctxs of
    Just t  -> goInferType $ Ind t m c a
    Nothing -> typeError FailedToInferType $ Just ("Unknown variable " ++ show x)

goInferType (Ind
  Nat
  (NoBind m)
  [NoBind c0, Bind w (Bind z (NoBind cs))]
  n)                                                    = goInferType (Ind Nat (Bind Nothing $ NoBind $ bumpUp m) [NoBind c0, Bind w (Bind z (NoBind cs))] n)

goInferType (Ind
  Nat
  (Bind x (NoBind m))
  [NoBind c0, Bind w (Bind z (NoBind cs))]
  n)                                                    = do
  ctxs <- ask

  (en, nt)   <- goCheckType n Nat
  (em, mt)   <- local (addToBoundCtx (x, Nat)) (goInferEvaluatedType m)
  (ec0, c0t) <- local useBoundCtx $ goCheckEvaluatedType c0 $ bumpDown $ open Zero em
  (ecs, cst) <- local (useBoundCtx . addToBoundCtx (z, em) . addToBoundCtx (w, Nat)) (goCheckEvaluatedType cs $ bumpUp $ open (Succ $ Var $ Bound 0) em)

  case mt of
    Univ _ -> return (Ind
      Nat
      (Bind x (NoBind em))
      [NoBind ec0, Bind w (Bind z (NoBind ecs))]
      en, bumpDown $ open (bumpUp en) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((x, Nat) : bctx ctxs) em ++ " is not a term of a universe")

goInferType (Ind t m c a)                              = typeError FailedToInferType $ Just ("Invalid induction " ++ show (Ind t m c a))

runCheckType :: Contexts -> MetaState -> Term -> Term -> CanError ((Term, Term), MetaState)
runCheckType ctxs st m mt = runStateT (runReaderT (goCheckType m mt) ctxs) st

evalCheckType :: Contexts -> MetaState -> Term -> Term -> CanError (Term, Term)
evalCheckType ctxs st m mt = evalStateT (runReaderT (goCheckType m mt) ctxs) st

goCheckType :: Term -> Term -> TypeCheck (Term, Term)
goCheckType m (Var (Free x))                             = do
  ctxs <- ask

  case lookup x $ env ctxs of
    Just t  -> do
      (em, _) <- goCheckType m t
      return (em, Var $ Free x)
    Nothing -> unifyInferredType m (Var $ Free x)

goCheckType (Lam (x, Just t, ex) m) (Pi (x', t', ex') n) = do
  ctxs <- ask

  (et, tt)   <- goInferEvaluatedType t
  (et', t't) <- local useTypeBoundCtx (goInferEvaluatedType t')
  (em, mt)   <- local (addToBoundCtxs (Just x, et) (x', et')) (goCheckType m n)

  case (tt, t't, ex == ex') of
    (_, _, False)       -> typeError TypeMismatch $ Just ("Mismatching explicitness between " ++ showTermWithContext (bctx ctxs) (Lam (x, Just et, ex) em) ++ " and " ++ showTermWithContext (tbctx ctxs) (Pi (x', et, ex') n))
    (Univ i, Univ j, _) -> do
      unify et et' Nothing
      return (Lam (x, Just et, ex) em, Pi (x', et, Exp) mt)
    (Univ _, _, _)      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et' ++ " is not a term of a universe")
    (_, _, _)           -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) et ++ " is not a term of a universe")

goCheckType (Lam (x, Nothing, ex) m) (Pi (x', t, ex') n) = do
  ctxs <- ask

  (et, tt) <- local useTypeBoundCtx (goInferEvaluatedType t)
  (em, mt) <- local (addToBoundCtxs (Just x, et) (x', et)) (goCheckType m n)

  case tt of
    Univ _ -> if ex == ex'
      then return (Lam (x, Nothing, ex) em, Pi (x', et, Exp) mt)
      else typeError TypeMismatch $ Just ("Mismatching explicitness between " ++ showTermWithContext (bctx ctxs) (Lam (x, Nothing, ex) em) ++ " and " ++ showTermWithContext (tbctx ctxs) (Pi (x', et, ex') n))
    _      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et ++ " is not a term of a universe")

goCheckType (Pair m n) (Sigma (x, t) t')                 = do
  ctxs <- ask

  (et, tt)   <- goInferEvaluatedType t
  (et', t't) <- local (addToBoundCtx (x, et) . useTypeBoundCtx) (goInferEvaluatedType t')
  (em, mt)   <- goCheckType m et
  (en, nt)   <- goCheckType n (bumpDown $ open (bumpUp em) et')

  case (tt, t't) of
    (Univ _, Univ _) -> return (Pair em en, Sigma (x, et) et')
    (Univ _, _)      -> typeError TypeMismatch $ Just (showTermWithContext ((x, et) : tbctx ctxs) et' ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et ++ " is not a term of a universe")

goCheckType (Inl m) (Sum t t')                           = do
  ctxs <- ask

  (em, mt)   <- goCheckType m t
  (et, tt)   <- local useTypeBoundCtx (goInferEvaluatedType t)
  (et', t't) <- local useTypeBoundCtx (goInferEvaluatedType t')

  case (tt, t't) of
    (Univ _, Univ _) -> return (Inl em, Sum et et')
    (Univ _, _)      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et' ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et ++ " is not a term of a universe")

goCheckType (Inr m) (Sum t t')                           = do
  ctxs <- ask

  (em, mt)   <- goCheckType m t'
  (et, tt)   <- local useTypeBoundCtx (goInferEvaluatedType t)
  (et', t't) <- local useTypeBoundCtx (goInferEvaluatedType t')

  case (tt, t't) of
    (Univ _, Univ _) -> return (Inr em, Sum et et')
    (Univ _, _)      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et' ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) et ++ " is not a term of a universe")

goCheckType m t                                          = unifyInferredType m t

unifyInferredType :: Term -> Term -> TypeCheck (Term, Term)
unifyInferredType m t = do
  ctxs <- ask

  (em, mt) <- goInferTypeAndElab m
  unify mt t $ Just ("The type of " ++ showTermWithContext (bctx ctxs) em ++ " is " ++ showTermWithContext (bctx ctxs) (eval mt) ++ " but expected " ++ showTermWithContext (tbctx ctxs) t)
  return (em, t)

goInferEvaluatedType :: Term -> TypeCheck (Term, Term)
goInferEvaluatedType m = do
  ctxs <- ask

  (em, mt) <- goInferTypeAndElab m
  return (em, eval $ resolve (env ctxs) mt)

goCheckEvaluatedType :: Term -> Term -> TypeCheck (Term, Term)
goCheckEvaluatedType m t = do
  ctxs <- ask

  goCheckType m (eval $ resolve (env ctxs) t)

instantiateImplicits :: Term -> Term -> TypeCheck (Term, Term)
instantiateImplicits em (Pi (x, t, Imp) t') = do
  ctxs <- ask

  mv <- createMetaVar t $ bctx ctxs
  let em'  = App em (mv, Imp)
  let em't = bumpDown $ open (bumpUp mv) t'
  instantiateImplicits em' em't
instantiateImplicits em mt                  = return (em, mt)

goInferTypeAndElab :: Term -> TypeCheck (Term, Term)
goInferTypeAndElab m = do
  (em, mt) <- goInferType m
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
