module Core.Program where

import Core.Term
import Core.Error
import Core.Judgement

import Control.Monad.Reader
import Data.ByteString.Lazy.Char8 (ByteString, unpack)

newtype Pragma
  = Check Term

data Declaration
  = Def Alias
  | Signature Assumption
  | Pragma Pragma

type Program = [Declaration]

run :: Program -> CanError ()
run p = runReader (runProgram p) ([], [])
  where
    runProgram :: Program -> Reader (Environment, Context) (CanError ())
    runProgram [] = return (Result ())

{-
oldRun :: Program -> CanError ()
oldRun = runWithContexts [] []
  where
    runWithContexts :: Environment -> Context -> Program -> CanError ()
    runWithContexts e g []     = return (Result ())
    runWithContexts e g (d:ds) = case d of
        Def (x, m)       -> case (lookup x e, lookup x g) of
          (Just _, _)  -> return (Error DuplicateDefinitions (Just ("Duplicate definintions of " ++ unpack x ++ " found")))
          (_, Just t)  -> case checkType e g m t of
            Result t'    -> runWithContexts ((x, unsafeEval e m) : e) ((x, t') : g) ds
            Error errc s -> return (Error errc s)
          (_, Nothing) -> case inferType e g m of
            Result t'    -> runWithContexts ((x, unsafeEval e m) : e) ((x, t') : g) ds
            Error errc s -> return (Error errc s)
        Signature (x, t) -> case (lookup x e, lookup x g) of
          (_, Just t') -> if t === t' $ g then p else return (Error TypeMismatch (Just ("The type of " ++ unpack x ++ " is " ++ show t' ++ " but expected " ++ show t)))
          _            -> p
          where p = runWithContexts e ((x, t) : g) ds
        Pragma (Check m) ->
          case inferType e g m of
            Result t    -> do
              runWithContexts e g ds
            Error err s -> return (Error err s)
-}

instance Show Declaration where
  show (Signature (x, t)) = unpack x ++ " : " ++ show t
  show (Def (x, m))  = unpack x ++ " := " ++ show m
  show (Pragma p)    = show p

instance Show Pragma where
  show (Check m) = "#check " ++ show m
