{-# LANGUAGE MultiParamTypeClasses #-}
module LambdaPi where

import Control.Monad.Except (MonadError (throwError), unless)
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Prelude hiding (lookup)

type Id = String

data TermType = I | C

data Term :: TermType -> * where
  Ann :: Term C -> Term C -> Term I
  Star :: Term I
  Pi :: Id -> Term C -> Term C -> Term I
  Sigma :: Id -> Term C -> Term C -> Term I
  Var :: Id -> Term I
  App :: Term I -> Term C -> Term I
  Nat :: Term I
  NatElim :: Term C -> Term C -> Term C -> Term C -> Term I
  Zero :: Term I
  Succ :: Term C -> Term I
  Eq :: Term C -> Term C -> Term C -> Term I
  EqElim :: Term C -> Term C -> Term C -> Term C -> Term C -> Term C -> Term I
  Let :: Id -> Term I -> Term C -> Term C
  Inf :: Term I -> Term C
  Lam :: Id -> Term C -> Term C
  Refl :: Term C -> Term C -> Term C
  Pair :: Term C -> Term C -> Term C
  Fst :: Term I -> Term I
  Snd :: Term I -> Term I

instance Show (Term a) where
  show (Ann t ty) = "(" ++ show t ++ ") : (" ++ show ty ++ ")"
  show Star = "*"
  show (Pi x ty t) = "Pi (" ++ x ++ " : " ++ show ty ++ ") (" ++ show t ++ ")"
  show (Var x) = x
  show (App m n) = show m ++ " " ++ show n
  show (Eq ty a b) = "Eq " ++ show ty ++ " " ++ show a ++ " " ++ show b
  show (Let x v t) = "Let " ++ show x ++ " = " ++ show v ++ " " ++ show t
  show (Inf t) = show t
  show (Lam x t) = "lambda " ++ x ++ ". " ++ show t
  show (Refl x ty) = "Refl " ++ show x ++ " " ++ show ty
  show (Pair t1 t2) = "(" ++ show t1 ++ " , " ++ show t2 ++ ")"
  show (Fst t) = "Fst (" ++ show t ++ ")"
  show (Snd t) = "Snd (" ++ show t ++ ")"
  show (Sigma x ty t) = "Sigma (" ++ x ++ " : " ++ show ty ++ ") (" ++ show t ++ ")"
  show Nat = "Nat"
  show NatElim {} = "NatElim"
  show Zero = "Zero"
  show (Succ n) = "Succ (" ++ show n ++ ")"
  show EqElim {} = "EqElim"

-- eval

data NFType = Value | Neutral

data NormalForm :: NFType -> * where
  VLam :: Id -> NormalForm Value -> NormalForm Value
  VStar :: NormalForm Value
  VPi :: Id -> NormalForm Value -> NormalForm Value -> NormalForm Value
  VSigma :: Id -> NormalForm Value -> NormalForm Value -> NormalForm Value
  VNat :: NormalForm Value
  VZero :: NormalForm Value
  VSucc :: NormalForm Value -> NormalForm Value
  VEq :: NormalForm Value -> NormalForm Value -> NormalForm Value -> NormalForm Value
  VRefl :: NormalForm Value -> NormalForm Value -> NormalForm Value
  VPair :: NormalForm Value -> NormalForm Value -> NormalForm Value
  VNeutral :: NormalForm Neutral -> NormalForm Value
  NFree :: Id -> NormalForm Neutral
  NApp :: NormalForm Neutral -> NormalForm Value -> NormalForm Neutral
  NNatElim :: NormalForm Value -> NormalForm Value -> NormalForm Value -> NormalForm Neutral -> NormalForm Neutral
  NFst :: NormalForm Neutral -> NormalForm Neutral
  NSnd :: NormalForm Neutral -> NormalForm Neutral

instance Eq (NormalForm a) where
  VLam x v == VLam x' v' = let z = genNameNotIn (fv v `Set.union` fv v') x in rename x z v == rename x' z v'
  VStar == VStar = True
  VPi x ty1 ty2 == VPi x' ty1' ty2' = let z = genNameNotIn (fv ty2 `Set.union` fv ty2') x in rename x z ty2 == rename x' z ty2'
  VSigma x ty1 ty2 == VSigma x' ty1' ty2' = let z = genNameNotIn (fv ty2 `Set.union` fv ty2') x in rename x z ty2 == rename x' z ty2'
  VNeutral n == VNeutral n' = n == n'
  VNat == VNat = True
  VZero == VZero = True
  VSucc v == VSucc v' = v == v'
  VEq ty a b == VEq ty' a' b' = ty == ty' && a == a' && b == b'
  VRefl ty a == VRefl ty' a' = ty == ty' && a == a'
  -- VPair v1 v2 == VPair v1' v2' = v1 == v1' && v2 == v2'
  VPair v1 v2 == p = evalFst p == v1 && evalSnd p == v2
  p == VPair v1 v2 = evalFst p == v1 && evalSnd p == v2
  NFree x == NFree x' = x == x'
  NApp n v == NApp n' v' = n == n' && v == v'
  NNatElim a b c d == NNatElim a' b' c' d' = a == a' && b == b' && c == c' && d == d'
  NFst n == NFst n' = n == n'
  NSnd n == NSnd n' = n == n'
  _ == _ = False

instance Show (NormalForm a) where
  show (VLam x v) = "λ" ++ x ++ ". " ++ show v
  show VStar = "*"
  show (VPi "_" ty ty') = show ty ++ " -> " ++ show ty'
  show (VPi x ty ty') = "Ɐ(" ++ x ++ " : " ++ show ty ++ "). " ++ show ty'
  show (VSigma "_" ty ty') = "(" ++ show ty ++ " , " ++ show ty' ++ ")"
  show (VSigma x ty ty') = "∃(" ++ x ++ " : " ++ show ty ++ "). " ++ show ty'
  show (VNeutral n) = show n
  show VNat = "Nat"
  show VZero = "Z"
  show (VSucc v) = "S (" ++ show v ++ ")"
  show (VEq _ x y) = show x ++ " = " ++ show y
  show (VRefl ty x) = "Refl " ++ show ty ++ " " ++ show x
  show (VPair v1 v2) = "(" ++ show v1 ++ " , " ++ show v2 ++ ")"
  show (NFree x) = x
  show (NApp n v) = "(" ++ show n ++ ") (" ++ show v ++ ")"
  show (NNatElim v1 v2 v3 n) = "NNatElim (" ++ show v1 ++ ") (" ++ show v2 ++ ") (" ++ show v3 ++ ") (" ++ show n ++ ")"
  show (NFst n) = "NFst " ++ show n
  show (NSnd n) = "NSnd " ++ show n

genNameNotIn :: Set.Set Id -> Id -> Id
genNameNotIn fvs x = case n of
  0 -> x
  _ -> x ++ show n
  where
    n = length $ takeWhile (`Set.member` fvs) $ x : map ((x ++) . show) [1 ..]

genName :: NormalForm Value -> Id -> Id
genName v = genNameNotIn (fv v)

vfree :: Id -> NormalForm Value
vfree x = VNeutral (NFree x)

rename :: Id -> Id -> NormalForm Value -> NormalForm Value
rename x x' = subst x (vfree x')

fv :: NormalForm a -> Set.Set Id
fv (VLam x v) = Set.delete x (fv v)
fv VStar = Set.empty
fv (VPi x v' v) = fv v' `Set.union` Set.delete x (fv v)
fv (VSigma x v' v) = fv v' `Set.union` Set.delete x (fv v)
fv (VNeutral n) = fv n
fv VNat = Set.empty
fv VZero = Set.empty
fv (VSucc v) = fv v
fv (VEq ty x y) = fv ty `Set.union` fv x `Set.union` fv y
fv (VRefl ty x) = fv ty `Set.union` fv x
fv (VPair v1 v2) = fv v1 `Set.union` fv v2
fv (NFree x) = Set.singleton x
fv (NApp n v) = fv n `Set.union` fv v
fv (NNatElim v1 v2 v3 n) = fv v1 `Set.union` fv v2 `Set.union` fv v3 `Set.union` fv n
fv (NFst n) = fv n
fv (NSnd n) = fv n

subst :: Id -> NormalForm Value -> NormalForm a -> NormalForm Value
subst x v (VLam y t) =
  if x == y
    then VLam y t
    else let y' = genName v y in VLam y' (subst x v $ rename y y' t)
subst x v VStar = VStar
subst x v (VPi y ty' ty) =
  let y' = genName ty y
   in VPi y' (subst x v ty') (subst x v $ rename y y' ty)
subst x v (VSigma y ty' ty) =
  let y' = genName ty y
   in VSigma y' (subst x v ty') (subst x v $ rename y y' ty)
subst x v (VNeutral n) = subst x v n
subst x v VNat = VNat
subst x v VZero = VZero
subst x v (VSucc v') = VSucc $ subst x v v'
subst x v (VEq ty a b) = VEq (subst x v ty) (subst x v a) (subst x v b)
subst x v (VRefl ty a) = VRefl (subst x v ty) (subst x v a)
subst x v (VPair v1 v2) = VPair (subst x v v1) (subst x v v2)
subst x v (NFree y) = if x == y then v else VNeutral (NFree y)
subst x v (NApp n v') = subst x v n `vapp` subst x v v'
subst x v (NNatElim m mz ms k) = evalNat (subst x v m) (subst x v mz) (subst x v ms) (subst x v k)
subst x v (NFst n) = evalFst $ subst x v n
subst x v (NSnd n) = evalSnd $ subst x v n

vapp :: NormalForm Value -> NormalForm Value -> NormalForm Value
vapp (VLam x v) v2 = subst x v2 v
vapp (VNeutral n) v2 = VNeutral (NApp n v2)
vapp _ _ = undefined

evalNat :: NormalForm Value -> NormalForm Value -> NormalForm Value -> NormalForm Value -> NormalForm Value
evalNat vm vmz vms VZero = vmz
evalNat vm vmz vms (VSucc l) = vms `vapp` l `vapp` evalNat vm vmz vms l
evalNat vm vmz vms (VNeutral n) = VNeutral $ NNatElim vm vmz vms n
evalNat _ _ _ _ = undefined

evalFst :: NormalForm Value -> NormalForm Value
evalFst (VPair v _) = v
evalFst (VNeutral n) = VNeutral (NFst n)
evalFst _ = undefined

evalSnd :: NormalForm Value -> NormalForm Value
evalSnd (VPair _ v) = v
evalSnd (VNeutral n) = VNeutral (NSnd n)
evalSnd _ = undefined

eval :: Ctx ctx Id (NormalForm Value) => ctx Id (NormalForm Value) -> Term a -> NormalForm Value
eval ctx (Ann t _) = eval ctx t
eval ctx Star = VStar
eval ctx (Pi x ty t) = VPi x (eval ctx ty) (eval (insert x (vfree x) ctx) t)
eval ctx (Sigma x ty t) = VSigma x (eval ctx ty) (eval (insert x (vfree x) ctx) t)
eval ctx (Var x) = fromMaybe (error $ "undefined variable: " ++ x) (lookup x ctx)
eval ctx (App t1 t2) = eval ctx t1 `vapp` eval ctx t2
eval ctx Nat = VNat
eval ctx Zero = VZero
eval ctx (Succ t) = VSucc $ eval ctx t
eval ctx (NatElim m mz ms k) = evalNat (eval ctx m) (eval ctx mz) (eval ctx ms) (eval ctx k)
eval ctx (Eq ty x y) = VEq (eval ctx ty) (eval ctx x) (eval ctx y)
eval ctx (EqElim ty m mrefl a b p) = eval ctx mrefl
eval ctx (Let x v t) = subst x (eval ctx v) (eval ctx t)
eval ctx (Inf t) = eval ctx t
eval ctx (Lam x t) = VLam x $ eval (insert x (vfree x) ctx) t
eval ctx (Refl ty x) = VRefl (eval ctx ty) (eval ctx x)
eval ctx (Fst t) = evalFst $ eval ctx t
eval ctx (Snd t) = evalSnd $ eval ctx t
eval ctx (Pair t1 t2) = VPair (eval ctx t1) (eval ctx t2)

-- type check & inference
type Type = NormalForm Value

class Ctx (ctx :: * -> * -> *) (k :: *) (v :: *) where
  lookup :: k -> ctx k v -> Maybe v
  insert :: k -> v -> ctx k v -> ctx k v

class (Ctx (TyCtx m) Id Type) => TyCtxReader (m :: * -> *) where
  type TyCtx m :: * -> * -> *
  askTyCtx :: m (TyCtx m Id Type)
  modifyTyCtx :: (TyCtx m Id Type -> TyCtx m Id Type) -> m a -> m a

class (Ctx (ValCtx m) Id (NormalForm Value)) => ValCtxReader (m :: * -> *) where
  type ValCtx m :: * -> * -> *
  askValCtx :: m (ValCtx m Id (NormalForm Value))
  modifyValCtx :: (ValCtx m Id (NormalForm Value) -> ValCtx m Id (NormalForm Value)) -> m a -> m a

type TcMonad m = (Monad m, TyCtxReader m, ValCtxReader m, MonadError String m)

evalM :: TcMonad m => Term a -> m (NormalForm Value)
evalM t = do
  ctx <- askValCtx
  return $ eval ctx t

lookupTy :: TcMonad m => Id -> m (Maybe Type)
lookupTy x = lookup x <$> askTyCtx

extTyCtx :: TcMonad m => Id -> Type -> m a -> m a
extTyCtx x ty = modifyTyCtx (insert x ty)

extValCtx :: TcMonad m => Id -> NormalForm Value -> m a -> m a
extValCtx x ty = modifyValCtx (insert x ty)

typeInfer :: TcMonad m => Term I -> m Type
typeInfer (Ann t ty) = do
  typeCheck ty VStar
  vty <- evalM ty
  typeCheck t vty
  return vty
typeInfer Star = return VStar
typeInfer (Pi x ty t) = do
  typeCheck ty VStar
  ty' <- evalM ty
  extValCtx x (vfree x) $ extTyCtx x ty' $ typeCheck t VStar
  return VStar
typeInfer (Sigma x ty t) = do
  typeCheck ty VStar
  ty' <- evalM ty
  extValCtx x (vfree x) $ extTyCtx x ty' $ typeCheck t VStar
  return VStar
typeInfer (Var x) = do
  result <- lookupTy x
  case result of
    Nothing -> throwError $ "unbound variable: " ++ x
    Just ty -> return ty
typeInfer t@(App t1 t2) = do
  ty1 <- typeInfer t1
  case ty1 of
    VPi x ty ty' -> do
      typeCheck t2 ty
      v2 <- evalM t2
      return $ subst x v2 ty'
    _ -> throwError $ "illegal application: " ++ show t
typeInfer Nat = return VStar
typeInfer Zero = return VNat
typeInfer (Succ t) = do
  typeCheck t VNat
  return VNat
typeInfer (NatElim m mz ms k) = do
  typeCheck m (VPi "a" VNat VStar)

  vm <- evalM m

  typeCheck mz (vm `vapp` VZero)

  let vml = vm `vapp` vfree "l"
  let vmsl = vm `vapp` VSucc (vfree "l")
  let tyMs = VPi "l" VNat (VPi "mk" vml vmsl)
  typeCheck ms tyMs

  typeCheck k VNat

  vk <- evalM k
  return $ vm `vapp` vk
typeInfer (Eq ty a b) = do
  typeCheck ty VStar
  vty <- evalM ty
  typeCheck a vty
  typeCheck b vty
  return VStar
typeInfer (EqElim ty m mrefl a b p) = do
  typeCheck ty VStar
  vty <- evalM ty
  -- m :: forall x y : ty, _ : x == y. *
  typeCheck m (VPi "x" vty (VPi "y" vty (VPi "_" (VEq vty (vfree "x") (vfree "y")) VStar)))
  vm <- evalM m
  -- mrefl :: forall z. m z z refl(z)
  typeCheck mrefl (VPi "z" vty (vm `vapp` vfree "z" `vapp` vfree "z" `vapp` VRefl vty (vfree "z")))
  typeCheck a vty
  typeCheck b vty
  va <- evalM a
  vb <- evalM b
  typeCheck p (VEq vty va vb)
  vp <- evalM p
  return $ vm `vapp` va `vapp` vb `vapp` vp
typeInfer (Fst t) = do
  ty <- typeInfer t
  case ty of
    VSigma _ ty' _ -> return ty'
    _ -> throwError $ "type mismatch: Sigma type vs " ++ show ty
typeInfer (Snd t) = do
  ty <- typeInfer t

  case ty of
    VSigma x ty' t' -> do
      vt <- evalM t
      return $ subst x (evalFst vt) t'
    _ -> throwError $ "type mismatch: Sigma type vs " ++ show ty

typeCheck :: TcMonad m => Term C -> Type -> m ()
typeCheck (Inf t) ty = do
  ty' <- typeInfer t
  unless (ty == ty') $ throwError $ "type mismatch: " ++ show ty ++ " (exceped) vs " ++ show ty' ++ " (infered)"
typeCheck (Lam x t) (VPi x' ty ty') = do
  let ty'' = rename x' x ty'
  extValCtx x (vfree x) $ extTyCtx x ty $ typeCheck t ty''
typeCheck (Refl ty a) (VEq vty' va' vb') = do
  typeCheck ty VStar
  vty <- evalM ty
  typeCheck a vty
  unless (vty == vty') $ throwError $ "type mismatch: " ++ show vty' ++ " (excepted) vs " ++ show vty ++ " (infered)"
  unless (va' == vb') $ throwError $ "Refl couldn't deduce to " ++ show (VEq vty' va' vb')
  va <- evalM a
  unless (va == va') $ throwError $ "type mismatch: " ++ show va' ++ " vs " ++ show va
-- let x = v in t : ty
typeCheck (Let x v t) ty = do
  ty' <- typeInfer v
  tyv <- evalM v
  extValCtx x tyv $ extTyCtx x ty' $ typeCheck t ty
-- (t1, t2) : \Sigma (x : ty) t
typeCheck (Pair t1 t2) (VSigma x ty t) = do
  typeCheck t1 ty
  vt1 <- evalM t1
  let vt = subst x vt1 t
  typeCheck t2 vt
typeCheck t ty = throwError $ "type mismatch: " ++ show t ++ " vs " ++ show ty

typeInferTerms :: TcMonad m => [(Id, Term I)] -> m [(Id, Type)]
typeInferTerms [] = return []
typeInferTerms ((x, term) : terms) = do
  ty <- typeInfer term
  vterm <- evalM term
  ts <- extValCtx x vterm $ extTyCtx x ty $ typeInferTerms terms
  return $ (x, ty) : ts
