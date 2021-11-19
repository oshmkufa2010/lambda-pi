module Main where

import Exp.Par (myLexer, pModule, pExp)
import LambdaPi (runTI, typeInferTerms)
import Resolver (resolveModule, runResolver)
import System.Environment (getArgs)

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
                      runTI $ typeInferTerms defs

      case result of
        Left err -> putStrLn err
        Right tys -> mapM_ (\(x, ty) -> putStrLn $ x ++ " : " ++ show ty) tys
    _ -> putStrLn $ "args error: " ++ show args
