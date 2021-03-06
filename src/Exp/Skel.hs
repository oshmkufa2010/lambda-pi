-- Haskell module generated by the BNF converter

{-# OPTIONS_GHC -fno-warn-unused-matches #-}

module Exp.Skel where

import Prelude (($), Either(..), String, (++), Show, show)
import qualified Exp.Abs

type Err = Either String
type Result = Err String

failure :: Show a => a -> Result
failure x = Left $ "Undefined case: " ++ show x

transAIdent :: Exp.Abs.AIdent -> Result
transAIdent x = case x of
  Exp.Abs.AIdent string -> failure x

transHoleIdent :: Exp.Abs.HoleIdent -> Result
transHoleIdent x = case x of
  Exp.Abs.HoleIdent string -> failure x

transModule :: Exp.Abs.Module -> Result
transModule x = case x of
  Exp.Abs.Module aident decls -> failure x

transDecl :: Exp.Abs.Decl -> Result
transDecl x = case x of
  Exp.Abs.DeclDef aident teles exp1 exp2 -> failure x

transExp :: Exp.Abs.Exp -> Result
transExp x = case x of
  Exp.Abs.Let decls exp -> failure x
  Exp.Abs.Lam aident aidents exp -> failure x
  Exp.Abs.Fun exp1 exp2 -> failure x
  Exp.Abs.Pi tele teles exp -> failure x
  Exp.Abs.Sigma tele teles exp -> failure x
  Exp.Abs.App exp1 exp2 -> failure x
  Exp.Abs.Id exp1 exp2 exp3 -> failure x
  Exp.Abs.IdJ exp1 exp2 exp3 exp4 exp5 exp6 -> failure x
  Exp.Abs.Refl exp1 exp2 -> failure x
  Exp.Abs.Fst exp -> failure x
  Exp.Abs.Snd exp -> failure x
  Exp.Abs.Pair exp exps -> failure x
  Exp.Abs.Var aident -> failure x
  Exp.Abs.U -> failure x
  Exp.Abs.Hole holeident -> failure x

transTele :: Exp.Abs.Tele -> Result
transTele x = case x of
  Exp.Abs.Tele aident aidents exp -> failure x
