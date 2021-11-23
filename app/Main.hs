{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Main where

import Control.Monad.Except (MonadError (..))
import Control.Monad.Reader (MonadReader (local), ReaderT (runReaderT), asks)
import qualified Data.Map as M
import Exp.Par (myLexer, pExp, pModule)
import LambdaPi (Id, NFType (..), NormalForm, Type, Ctxable (..), typeInferTerms)
import Resolver (resolveModule, runResolver)
import System.Environment (getArgs)

data Env = Env {typeEnv :: M.Map Id Type, valEnv :: M.Map Id (NormalForm Value)}

updateTypeEnv :: (M.Map Id Type -> M.Map Id Type) -> Env -> Env
updateTypeEnv f Env {typeEnv = te, valEnv = ve} = Env {typeEnv = f te, valEnv = ve}

updateValEnv :: (M.Map Id Type -> M.Map Id Type) -> Env -> Env
updateValEnv f Env {typeEnv = te, valEnv = ve} = Env {typeEnv = te, valEnv = f ve}

newtype App a = App {getApp :: ReaderT Env (Either String) a}
  deriving (Functor, Applicative, Monad, MonadError String, MonadReader Env)

instance Ctxable App where
  askTyCtx = asks typeEnv
  extTyCtx x ty ma = local (updateTypeEnv (M.insert x ty)) ma
  askValCtx = asks valEnv
  extValCtx x v ma = local (updateValEnv (M.insert x v)) ma

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
