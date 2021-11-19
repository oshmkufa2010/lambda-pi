{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}

module Resolver where

import Control.Monad.Except (MonadError (throwError), when)
import Control.Monad.State (StateT, evalStateT, modify)
import Data.Functor ((<&>))
import qualified Data.Map as M
import qualified Exp.Abs as E
import LambdaPi

type Resolver a = Either String a

runResolver :: Resolver a -> Either String a
runResolver x = x

getName :: E.AIdent -> Id
getName (E.AIdent (_, name)) = name

resolveDecl :: E.Decl -> Resolver (Id, Term I)
resolveDecl (E.DeclDef ident teles retType def) = do
  -- f (A : U) (a : A) : A = a
  -- f : Pi (A : U) -> Pi (A : U) -> Pi (a : A) -> A
  let name = getName ident
  retType' <- resolveIExp retType
  teles' <- resolveTeles teles
  let piTy = foldr (\(id, t) ty -> Pi id (Inf t) (Inf ty)) retType' teles'
  body <- resolveCExp def
  let lamBody = foldr (\(x, _) e -> Lam x e) body teles'
  return (name, Ann lamBody (Inf piTy))

resolveIExp :: E.Exp -> Resolver (Term I)
resolveIExp (E.Fun e1 e2) = do
  t1 <- resolveIExp e1
  t2 <- resolveIExp e2
  return $ Pi "_" (Inf t1) (Inf t2)
resolveIExp (E.Pi tele teles retType) = do
  teles' <- resolveTeles (tele : teles)
  retType' <- resolveIExp retType
  return $ foldr (\(id, t) ty -> Pi id (Inf t) (Inf ty)) retType' teles'
resolveIExp (E.Sigma tele teles retType) = do
  teles' <- resolveTeles (tele : teles)
  retType' <- resolveIExp retType
  return $ foldr (\(id, t) ty -> Sigma id (Inf t) (Inf ty)) retType' teles'
resolveIExp (E.App e1 e2) = App <$> resolveIExp e1 <*> resolveCExp e2
resolveIExp (E.Id e1 e2 e3) = Eq <$> resolveCExp e1 <*> resolveCExp e2 <*> resolveCExp e3
resolveIExp (E.IdJ e1 e2 e3 e4 e5 e6) = EqElim <$> resolveCExp e1 <*> resolveCExp e2 <*> resolveCExp e3 <*> resolveCExp e4 <*> resolveCExp e5 <*> resolveCExp e6
resolveIExp (E.Var x) = return $ Var (getName x)
resolveIExp E.U = return Star
resolveIExp (E.Fst e) = Fst <$> resolveIExp e
resolveIExp (E.Snd e) = Snd <$> resolveIExp e
resolveIExp _ = throwError "syntax error"

resolveCExp :: E.Exp -> Resolver (Term C)
resolveCExp (E.Lam x xs e) = do
  body <- resolveCExp e
  return $ foldr (Lam . getName) body (x : xs)
resolveCExp (E.Refl e1 e2) = Refl <$> resolveCExp e1 <*> resolveCExp e2
resolveCExp (E.Let decls e) = do
  xs <- mapM resolveDecl decls
  e' <- resolveCExp e
  return $ foldr (\(id, t) acc -> Let id t acc) e' xs
resolveCExp (E.Pair e es) = do
  t <- resolveCExp e
  ts <- mapM resolveCExp es
  return $ foldr1 Pair (t : ts)
resolveCExp t = Inf <$> resolveIExp t

resolveTele :: E.Tele -> Resolver [(Id, Term I)]
resolveTele (E.Tele x xs ty) = do
  ty' <- resolveIExp ty
  return $ map (\y -> (getName y, ty')) (x : xs)

resolveTeles :: [E.Tele] -> Resolver [(Id, Term I)]
resolveTeles teles = concat <$> mapM resolveTele teles

resolveModule :: E.Module -> Resolver (Id, [(Id, Term I)])
resolveModule (E.Module moduleName decls) = do
  xs <- mapM resolveDecl decls
  return (getName moduleName, xs)
