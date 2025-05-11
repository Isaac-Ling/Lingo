module Core.Execution where

import Core.Data
import Core.Error
import Core.Judgement

import Data.ByteString.Lazy.Char8 (ByteString, unpack)

run :: Program -> IO (CanError ())
run = runWithContexts [] []
  where
    runWithContexts :: Environment -> Context -> Program -> IO (CanError ())
    runWithContexts e g []     = return (Result ())
    runWithContexts e g (d:ds) = case d of
      Def (x, m)       -> case (lookup x e, lookup x g) of
        (Just _, _)  -> return (Error DuplicateDefinitions (Just ("Duplicate definintions of " ++ unpack x ++ " found")))
        (_, Just t)  -> case checkType g m t of
          Result t'    -> runWithContexts ((x, unsafeEval e m) : e) ((x, t') : g) ds
          Error errc s -> return (Error errc s)
        (_, Nothing) -> case inferType g m of
          Result t'    -> runWithContexts ((x, unsafeEval e m) : e) ((x, t') : g) ds
          Error errc s -> return (Error errc s)
      Signature (x, t) -> case (lookup x e, lookup x g) of
        (_, Just t') -> if t == t' then p else return (Error TypeMismatch (Just ("The type of " ++ unpack x ++ " is " ++ show t' ++ " but expected " ++ show t)))
        _            -> p
        where p = runWithContexts e ((x, t) : g) ds
      Pragma (Check m) ->
        case inferType g m of
          Result t    -> do
            putStrLn (show m ++ " := " ++ show (unsafeEval e m) ++ " : " ++ show t)
            runWithContexts e g ds
          Error err s -> return (Error err s)

instance Show Declaration where
  show (Signature (x, t)) = unpack x ++ " : " ++ show t
  show (Def (x, m))  = unpack x ++ " := " ++ show m
  show (Pragma p)    = show p

instance Show Pragma where
  show (Check m) = "#check " ++ show m
