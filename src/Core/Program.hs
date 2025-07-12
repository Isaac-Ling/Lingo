module Core.Program where

import Core.Term
import Core.Error
import Core.Judgement.Utils
import Core.Judgement.Typing
import Core.Judgement.Evaluation
import IO.Source ( readSource )
import Parsing.Parser

import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString, unpack)

type Runtime a = ReaderT (Environment, Context) (CanErrorT IO) a

run :: Program -> IO (CanError ())
run p = runCanErrorT $ runReaderT (go p) ([], [])
  where
    go :: Program -> Runtime ()
    go []                    = success

    go (Def (x, m'):ds)       = do
      (env, ctx) <- ask

      case lookup x env of
        Just _ -> abort DuplicateDefinitions (Just ("Duplicate definintions of " ++ unpack x ++ " found"))
        _      -> success

      let m = toDeBruijn m'

      t <- case lookup x ctx of
        Just t -> tryRun $ checkType env ctx m t
        _      -> tryRun $ inferType env ctx m

      local (addToRuntime (x, m) (x, t)) (go ds)

    go (Signature (x, t'):ds) = do
      (env, ctx) <- ask

      let t = toDeBruijn t'
      tt <- tryRun $ inferType env ctx t
      let p = local (addToCtx (x, t)) (go ds)

      case lookup x ctx of
        Just t2 -> if equal env t t2
          then p
          else abort TypeMismatch (Just ("The type of " ++ unpack x ++ " is " ++ show t ++ " but expected " ++ show t2))
        _       -> p

    go (Pragma (Check m'):ds) = do
      (env, ctx) <- ask

      let m = toDeBruijn m'
      t <- tryRun $ inferType env ctx m
      let ert = eval $ elaborate env m
      liftIO $ putStrLn (show m ++ " =>* " ++ show ert ++ " : " ++ show t)

      go ds

    go (Pragma (Include f):ds) = do
      (env, ctx) <- ask

      let file = f ++ ".lingo"

      msource <- liftIO $ readSource file
      source <- case msource of
        Result s -> return s
        err      -> lift $ CanErrorT $ return err

      program <- case parse source of
        Result p -> return p
        err      -> lift $ CanErrorT $ return err

      go (program ++ ds)

tryRun :: CanError a -> Runtime a
tryRun = lift . CanErrorT . return

success :: Runtime ()
success = return ()

abort :: ErrorCode -> Maybe String -> Runtime ()
abort errc ms = lift $ CanErrorT $ return $ Error errc ms

addToEnv :: Alias -> ((Environment, a) -> (Environment, a))
addToEnv def (env, a) = (def : env, a)

addToCtx :: Assumption -> ((a, Context) -> (a, Context))
addToCtx sig (a, ctx) = (a, sig : ctx)

addToRuntime :: Alias -> Assumption -> ((Environment, Context) -> (Environment, Context))
addToRuntime def sig = addToCtx sig . addToEnv def

instance Show Declaration where
  show (Signature (x, t')) = unpack x ++ " : " ++ show (toDeBruijn t')
  show (Def (x, m'))  = unpack x ++ " := " ++ show (toDeBruijn m')
  show (Pragma p)    = show p

instance Show Pragma where
  show (Check m') = "#check " ++ show (toDeBruijn m')
