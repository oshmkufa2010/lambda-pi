{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import Control.Monad.Except (MonadError (..))
import Control.Monad.Reader (MonadReader (local), ReaderT (runReaderT), asks)
import qualified Data.Map as M
import Exp.Par (myLexer, pExp, pModule)
import LambdaPi (Id, NFType (..), NormalForm, Type, Ctx (..), TyCtxReader (..), ValCtxReader (..), typeInferTerms)
import Resolver (resolveModule, runResolver)
import System.Environment (getArgs)

data Env = Env {typeEnv :: M.Map Id Type, valEnv :: M.Map Id (NormalForm Value)}

newtype App a = App {getApp :: ReaderT Env (Either String) a}
  deriving (Functor, Applicative, Monad, MonadError String, MonadReader Env)

instance Ctx M.Map Id Type where
  lookup = M.lookup
  insert = M.insert

instance TyCtxReader App where
  type TyCtx App = M.Map
  askTyCtx = asks typeEnv
  modifyTyCtx f = local (\env -> env{ typeEnv = f (typeEnv env) })

instance ValCtxReader App where
  type ValCtx App = M.Map
  askValCtx = asks valEnv
  modifyValCtx f = local (\env -> env{ valEnv = f (valEnv env) })

runApp :: App a -> Either String a
runApp (App tc) = runReaderT tc $ Env {typeEnv = M.empty, valEnv = M.empty}

main :: IO ()
main = do
  args <- getArgs
  case args of
    "tc" : filePath : _ -> do
      content <- readFile filePath
      let ts = myLexer content
      let result = do
            tree <- pModule ts
            (moduleName, defs) <- runResolver $ resolveModule tree
            runApp $ typeInferTerms defs

      case result of
        Left err -> putStrLn err
        Right tys -> mapM_ (\(x, ty) -> putStrLn $ x ++ " : " ++ show ty) tys
    _ -> putStrLn $ "args error: " ++ show args
