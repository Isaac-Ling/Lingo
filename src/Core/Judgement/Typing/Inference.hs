module Core.Judgement.Typing.Inference (inferType, checkType) where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Evaluation
import Core.Judgement.Typing.Context
import Core.Judgement.Typing.Unification

import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.ByteString.Lazy.Char8 (ByteString)

inferType :: Environment -> Context -> Term -> CanError (Term, Term)
inferType env ctx m = do
  result <- runStateT (runReaderT (runInferType m) initContexts) initState
  msol   <- solveConstraints env $ mcsts $ snd result
  let ts = fst result
  let e  = expandMetas msol $ fst ts
  let t  = expandMetas msol $ snd ts
  return (e, t)
  where
    initContexts = Contexts { env=env, ctx=ctx, bctx=[], tbctx=[] }
    initState    = MetaState { mcsts=[], mctx=[], metaID=0 }

checkType :: Environment-> Context -> Term -> Term -> CanError (Term, Term)
checkType env ctx m t = do
  result <- runStateT (runReaderT (runCheckType m t) initContexts) initState
  msol   <- solveConstraints env $ mcsts $ snd result
  let ts = fst result
  let e  = expandMetas msol $ fst ts
  let t  = expandMetas msol $ snd ts
  return (e, t)
  where
    initContexts = Contexts { env=env, ctx=ctx, bctx=[], tbctx=[] }
    initState    = MetaState { mcsts=[], mctx=[], metaID=0 }

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

runInferType (Var (Meta i))                            = do
  st <- get

  case lookup i $ mctx st of
    Just t  -> return (Var $ Meta i, t)
    Nothing -> typeError FailedToInferType $ Just ("Unknown meta variable " ++ show (Var $ Meta i))

runInferType (Pi (x, t, ex) m)                         = do
  ctxs <- ask

  (et, tt) <- runInferType t
  (em, mt) <- local (addToBoundCtx (x, t)) (runInferType m)

  case (tt, mt) of
    (Univ i, Univ j) -> return (Pi (x, et, ex) em, Univ $ max i j)
    (Univ i, _)      -> typeError TypeMismatch $ Just (showTermWithContext ((x, t) : bctx ctxs) m ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (show t ++ " is not a term of a universe")

runInferType (Sigma (x, t) m)                          = do
  ctxs <- ask

  (et, tt) <- runInferType t
  (em, mt) <- local (addToBoundCtx (x, t)) (runInferType m)

  case (tt, mt) of
    (Univ i, Univ j) -> return (Sigma (x, et) em, Univ $ max i j)
    (Univ i, _)      -> typeError TypeMismatch $ Just (showTermWithContext ((x, t) : bctx ctxs) m ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (show t ++ " is not a term of a universe")

runInferType (Lam (x, Just t, ex) m)                   = do
  ctxs <- ask

  (et, tt) <- runInferType t
  (em, mt) <- local (addToBoundCtx (Just x, t)) (runInferType m)

  case tt of
    Univ i -> return (Lam (x, Just et, ex) em, Pi (if isBinderUsed mt then Just x else Nothing, et, ex) mt)
    _      -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) t ++ " is not a term of a universe")

runInferType (Lam (x, Nothing, ex) m)                  = do
  ctxs <- ask

  typeError FailedToInferType $ Just ("Cannot infer type of implicit lambda " ++ showTermWithContext (bctx ctxs) (Lam (x, Nothing, ex) m))

runInferType (App m (n, ex))                           = do
  (em, mt) <- runInferType m
  inferAppType em (n, ex) mt
    where
      inferAppType :: Term -> (Term, Explicitness) -> Term -> TypeCheck (Term, Term)
      inferAppType m (n, ex') mt = do
        ctxs <- ask

        case mt of
          Pi (x, t, Exp) t' -> do
            (en, nt) <- runInferType n

            unify t nt $ Just (showTermWithContext (bctx ctxs) m ++ " of type " ++ showTermWithContext (bctx ctxs) mt ++ " cannot be applied to " ++ showTermWithContext (bctx ctxs) n ++ " of type " ++ showTermWithContext (bctx ctxs) nt)
            return (App m (en, ex'), bumpDown $ open (bumpUp en) t')
          Pi (x, t, Imp) t' -> do
            if ex == Imp
            then do
              -- If user supplies implicit variable explicitely, simply infer type using
              -- explicit type and term
              (_, at) <- inferAppType m (n, Exp) $ Pi (x, t, Exp) t'
              return (App m (n, Imp), at)
            else do
              -- Otherwise, create a meta variable and continue with type inference
              mv <- createMetaVar t
              let m'  = App m (mv, Imp)
              let m't = bumpDown $ open mv t'

              inferAppType m' (n, ex) m't
          _                 -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) m ++ " is not a term of a Pi type")

runInferType (Pair m n)                                = do
  (em, mt) <- runInferType m
  (en, nt) <- runInferType n

  return (Pair em en, Sigma (Nothing, mt) nt)

runInferType (Sum m n)                                 = do
  ctxs <- ask

  (em, mt) <- runInferType m
  (en, nt) <- runInferType n

  case (mt, nt) of
    (Univ i, Univ j) -> return (Sum em en, Univ $ max i j)
    (Univ i, _)      -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) n ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (show m ++ " is not a term of a universe")

runInferType (Inl m)                                   = do
  ctxs <- ask

  typeError FailedToInferType $ Just ("Cannot infer type of ambiguous injection " ++ showTermWithContext (bctx ctxs) (Inl m))

runInferType (Inr m)                                   = do
  ctxs <- ask

  typeError FailedToInferType $ Just ("Cannot infer type of ambiguous injection " ++ showTermWithContext (bctx ctxs) (Inr m))

runInferType Zero                                      = return (Zero, Nat)

runInferType (Succ m)                                  = do
  ctxs <- ask

  (em, mt) <- runInferType m

  case mt of
    Nat -> return (em, Nat)
    _   -> typeError FailedToInferType $ Just ("Cannot apply succ to a term of type " ++ showTermWithContext (bctx ctxs) mt)

runInferType (Funext p)                                = do
  ctxs <- ask

  (ep, pt) <- runInferType p

  case pt of
    Pi _ (Id _ (App f (Var (Bound 0), Exp)) (App g (Var (Bound 0), Exp))) -> do
      at  <- runInferType $ App f (Var (Bound 0), Exp)
      at' <- runInferType $ App g (Var (Bound 0), Exp)
      return (Funext ep, Id Nothing f g)
    _                                                                     -> typeError FailedToInferType $ Just ("Cannot apply funext to a term of type " ++ showTermWithContext (bctx ctxs) pt)

-- TODO: Type check univalence
runInferType (Univalence f)                            = do
  ctxs <- ask

  (ef, ft) <- runInferType f

  case ft of
    Top -> return (Univalence ef, Top)
    _   -> typeError FailedToInferType $ Just ("Cannot apply funext to a term of type " ++ showTermWithContext (bctx ctxs) ft)

runInferType (IdFam t)                                 = do
  ctxs <- ask

  (et, tt) <- runInferType t
  case tt of
    Univ i -> return (IdFam et, Pi (Nothing, et, Exp) $ Pi (Nothing, et, Exp) tt)
    _      -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) t ++ " is not a term of a universe")

runInferType (Id Nothing m n)                          = do
  (em, mt)   <- runInferType m
  (emt, mtt) <- runInferType mt
  (en, nt)   <- runCheckEvaluatedType n mt

  return (Id Nothing em en, mtt)

runInferType (Id (Just t) m n)                         = runCheckEvaluatedType (Id Nothing m n) t

runInferType (Refl m)                                  = do
  (em, mt) <- runInferType m

  return (Refl em, Id Nothing em em)

runInferType (Ind Bot (NoBind m) [] a)                 = runInferType (Ind Bot (Bind Nothing $ NoBind $ bumpUp m) [] a)

runInferType (Ind Bot (Bind x (NoBind m)) [] a)        = do
  ctxs <- ask

  (em, mt) <- local (addToBoundCtx (x, Bot)) (runInferType m)
  (ea, at) <- runCheckType a Bot

  case mt of
    Univ _ -> return (Ind Bot (Bind x (NoBind em)) [] ea, bumpDown $ open (bumpUp ea) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((x, Bot) : bctx ctxs) m ++ " is not a term of a universe")

runInferType (Ind Top (NoBind m) [NoBind c] a)          = runInferType (Ind Top (Bind Nothing $ NoBind $ bumpUp m) [NoBind c] a)

runInferType (Ind Top (Bind x (NoBind m)) [NoBind c] a) = do
  ctxs <- ask

  (em, mt) <- local (addToBoundCtx (x, Top)) (runInferType m)
  (ec, ct) <- local useBoundCtx $ runCheckEvaluatedType c (bumpDown $ open Star m)
  (ea, at) <- runCheckType a Top

  case mt of
    Univ _ -> return (Ind Top (Bind x (NoBind em)) [NoBind ec] ea, bumpDown $ open (bumpUp ea) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((x, Top) : bctx ctxs) m ++ " is not a term of a universe")

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

  (em, mt) <- local (addToBoundCtx (z, Sigma (x, t) n)) (runInferType m)
  (ef, ft) <- local (useBoundCtx . addToBoundCtx (y, n) . addToBoundCtx (w, t)) (runCheckEvaluatedType f $ openFor (Pair (Var $ Bound 1) (Var $ Bound 0)) 1 (bumpUp m))
  (ea, at) <- runCheckEvaluatedType a (Sigma (x, t) n)

  case mt of
    Univ _ -> return (Ind
      (Sigma (x, t) n)
      (Bind z (NoBind em))
      [Bind w (Bind y (NoBind ef))]
      ea, bumpDown $ open (bumpUp ea) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((z, Sigma (x, t) n) : bctx ctxs) m ++ " is not a term of a universe")

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

  (em, mt) <- local (addToBoundCtx (z, Sum t n)) (runInferType m)
  (ec, ct) <- local (useBoundCtx . addToBoundCtx (x, t)) (runCheckEvaluatedType c $ open (Inl $ Var $ Bound 1) m)
  (ed, dt) <- local (useBoundCtx . addToBoundCtx (y, n)) (runCheckEvaluatedType d $ open (Inr $ Var $ Bound 1) m)
  (ea, at) <- runCheckEvaluatedType a (Sum t n)

  case mt of
    Univ _ -> return (Ind
      (Sum t n)
      (Bind z (NoBind em))
      [Bind x (NoBind ec), Bind y (NoBind ed)]
      ea, bumpDown $ open (bumpUp ea) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((z, Sum t n) : bctx ctxs) m ++ " is not a term of a universe")

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

  (em, mt)   <- local (addToBoundCtx (p, Id (Just $ shift 2 t) (Var $ Bound 2) (Var $ Bound 1)) . addToBoundCtx (y, bumpUp t) . addToBoundCtx (x, t)) (runInferType m)
  (ec, ct)   <- local (useBoundCtx . addToBoundCtx (z, t)) (runCheckEvaluatedType c $ shift (-2) $ openFor (Var $ Bound 2) 2 $ openFor (Var $ Bound 2) 1 $ open (Refl $ Var $ Bound 2) m)
  (ep', p't) <- local useBoundCtx $ runCheckEvaluatedType p' (Id (Just t) a b)

  case mt of
    Univ _ -> return (Ind
      (IdFam t)
      (Bind x (Bind y (Bind p (NoBind em))))
      [Bind z (NoBind ec), NoBind ea, NoBind eb]
      ep', shift (-3) $ openFor (shift 3 ea) 2 $ openFor (shift 3 eb) 1 $ open (shift 3 ep') em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((p, Id (Just $ shift 2 t) (Var $ Bound 2) (Var $ Bound 1)) : (y, bumpUp t) : (x, t) : bctx ctxs) m ++ " is not a term of a universe")

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
  (em, mt)   <- local (addToBoundCtx (x, Nat)) (runInferType m)
  (ec0, c0t) <- local useBoundCtx $ runCheckEvaluatedType c0 $ bumpDown $ open Zero m
  (ecs, cst) <- local (useBoundCtx . addToBoundCtx (z, m) . addToBoundCtx (w, Nat)) (runCheckEvaluatedType cs $ bumpUp $ open (Succ $ Var $ Bound 0) m)

  case mt of
    Univ _ -> return (Ind
      Nat
      (Bind x (NoBind em))
      [NoBind ec0, Bind w (Bind z (NoBind ecs))]
      en, bumpDown $ open (bumpUp en) em)
    _      -> typeError TypeMismatch $ Just (showTermWithContext ((x, Nat) : bctx ctxs) m ++ " is not a term of a universe")

runInferType (Ind t m c a)                              = typeError FailedToInferType $ Just ("Invalid induction " ++ show (Ind t m c a))

runCheckEvaluatedType :: Term -> Term -> TypeCheck (Term, Term)
runCheckEvaluatedType m t = do
  ctxs <- ask

  runCheckType m (eval $ resolve (env ctxs) t)

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

  (et, tt)   <- runInferType t
  (et', t't) <- local useTypeBoundCtx (runInferType t')
  (em, mt)   <- local (addToBoundCtxs (Just x, t) (x', t')) (runCheckType m n)

  case (tt, t't, ex == ex') of
    (_, _, False)       -> typeError TypeMismatch $ Just ("Mismatching explicitness between " ++ showTermWithContext (bctx ctxs) (Lam (x, Just t, ex) m) ++ " and " ++ showTermWithContext (tbctx ctxs) (Pi (x', t, ex') n))
    (Univ i, Univ j, _) -> do
      unify t t' Nothing
      return (Lam (x, Just et, ex) em, Pi (x', et, Exp) mt)
    (Univ _, _, _)      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t' ++ " is not a term of a universe")
    (_, _, _)           -> typeError TypeMismatch $ Just (showTermWithContext (bctx ctxs) t ++ " is not a term of a universe")

runCheckType (Lam (x, Nothing, ex) m) (Pi (x', t, ex') n) = do
  ctxs <- ask

  (et, tt) <- local useTypeBoundCtx (runInferType t)
  (em, mt) <- local (addToBoundCtxs (Just x, t) (x', t)) (runCheckType m n)

  case tt of
    Univ _ -> if ex == ex'
      then return (Lam (x, Nothing, ex) em, Pi (x', t, Exp) mt)
      else typeError TypeMismatch $ Just ("Mismatching explicitness between " ++ showTermWithContext (bctx ctxs) (Lam (x, Nothing, ex) m) ++ " and " ++ showTermWithContext (tbctx ctxs) (Pi (x', t, ex') n))
    _      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t ++ " is not a term of a universe")

runCheckType (Pair m n) (Sigma (x, t) t')                 = do
  ctxs <- ask

  (et, tt)   <- runInferType t
  (et', t't) <- local (addToBoundCtx (x, t) . useTypeBoundCtx) (runInferType t')
  (em, mt)   <- runCheckType m t
  (en, nt)   <- runCheckType n (bumpDown $ open (bumpUp m) t')

  case (tt, t't) of
    (Univ _, Univ _) -> return (Pair em en, Sigma (x, t) t')
    (Univ _, _)      -> typeError TypeMismatch $ Just (showTermWithContext ((x, t) : tbctx ctxs) t' ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t ++ " is not a term of a universe")

runCheckType (Inl m) (Sum t t')                           = do
  ctxs <- ask

  (em, mt)   <- runCheckType m t
  (et, tt)   <- local useTypeBoundCtx (runInferType t)
  (et', t't) <- local useTypeBoundCtx (runInferType t')

  case (tt, t't) of
    (Univ _, Univ _) -> return (Inl em, Sum t t')
    (Univ _, _)      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t' ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t ++ " is not a term of a universe")

runCheckType (Inr m) (Sum t t')                           = do
  ctxs <- ask

  (em, mt)   <- runCheckType m t'
  (et, tt)   <- local useTypeBoundCtx (runInferType t)
  (et', t't) <- local useTypeBoundCtx (runInferType t')

  case (tt, t't) of
    (Univ _, Univ _) -> return (Inr em, Sum t t')
    (Univ _, _)      -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t' ++ " is not a term of a universe")
    (_, _)           -> typeError TypeMismatch $ Just (showTermWithContext (tbctx ctxs) t ++ " is not a term of a universe")

runCheckType m t                                          = unifyInferredType m t

unifyInferredType :: Term -> Term -> TypeCheck (Term, Term)
unifyInferredType m t = do
  ctxs <- ask

  (em, mt) <- runInferType m
  unify mt t $ Just ("The type of " ++ showTermWithContext (bctx ctxs) m ++ " is " ++ showTermWithContext (bctx ctxs) (eval mt) ++ " but expected " ++ showTermWithContext (tbctx ctxs) t)
  return (em, t)
