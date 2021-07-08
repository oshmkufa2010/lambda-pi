{-# LANGUAGE LambdaCase #-}

module LambdaPi where

import Control.Monad.Except (MonadError (throwError))
import Control.Monad.State
import Data.Either (fromRight)
import qualified Data.Map as M
import qualified Data.Set as Set

type Id = String

type Result = Either String

infixl 2 :@:

infix 1 :::

data ITerm
  = CTerm ::: CTerm
  | Star
  | Pi Id CTerm CTerm
  | Var Id
  | ITerm :@: CTerm
  | Nat
  | NatElim CTerm CTerm CTerm CTerm
  | Zero
  | Succ CTerm
  deriving (Eq, Show)

data CTerm
  = Inf ITerm
  | Lam Id CTerm
  deriving (Eq, Show)

-- eval

data Value
  = VLam Id Value
  | VStar
  | VPi Id Value Value
  | VNat
  | VZero
  | VSucc Value
  | VNeutral Neutral

instance Eq Value where
  VLam x v == VLam x' v' = either (const False) (== v') (rename x x' v)
  VStar == VStar = True
  VPi x ty1 ty2 == VPi x' ty1' ty2' = fromRight False result
    where
      result :: Result Bool
      result = do
        unless (ty1 == ty1') $ throwError ""
        ty2'' <- rename x x' ty2
        return (ty2'' == ty2')
  VNeutral n == VNeutral n' = n == n'
  VNat == VNat = True
  VZero == VZero = True
  VSucc v == VSucc v' = v == v'
  _ == _ = False

data Neutral
  = NFree Id
  | NApp Neutral Value
  | NNatElim Value Value Value Neutral
  deriving (Eq)

instance Show Value where
  show (VLam x v) = "λ" ++ x ++ ". " ++ show v
  show VStar = "*"
  show (VPi x ty ty') = "Ɐ(" ++ x ++ " : " ++ show ty ++ "). " ++ show ty'
  show (VNeutral n) = show n
  show VNat = "Nat"
  show VZero = "Z"
  show (VSucc v) = "S (" ++ show v ++ ")"

instance Show Neutral where
  show (NFree x) = x
  show (NApp n v) = "(" ++ show n ++ ") (" ++ show v ++ ")"
  show (NNatElim v1 v2 v3 n) = "NNatElim (" ++ show v1 ++ ") (" ++ show v2 ++ ") (" ++ show v3 ++ ") (" ++ show n ++ ")"

class Substable a where
  fv :: a -> Set.Set Id
  subst :: Id -> Value -> a -> Result Value

genName :: Value -> Id -> Id
genName v x = case n of
  0 -> x
  _ -> x ++ show n
  where
    n = length $ takeWhile (`Set.member` fv v) $ x : map ((x ++) . show) [1 ..]

vfree :: Id -> Value
vfree x = VNeutral (NFree x)

rename :: Id -> Id -> Value -> Result Value
rename x x' = subst x (vfree x')

vapp :: Value -> Value -> Result Value
vapp (VLam x v) v2 = subst x v2 v
vapp (VNeutral n) v2 = return $ VNeutral (NApp n v2)
vapp _ _ = throwError "illegal application"

vappM :: Result Value -> Result Value -> Result Value
vappM v1m v2m = join $ vapp <$> v1m <*> v2m

evalNat :: Value -> Value -> Value -> Value -> Result Value
evalNat vm vmz vms VZero = return vmz
evalNat vm vmz vms (VSucc l) = vms `vapp` l `vappM` evalNat vm vmz vms l
evalNat vm vmz vms (VNeutral n) = return $ VNeutral $ NNatElim vm vmz vms n
evalNat _ _ _ _ = throwError "illegal application"

evalNatM :: Result Value -> Result Value -> Result Value -> Result Value -> Result Value
evalNatM v1 v2 v3 v4 = join $ evalNat <$> v1 <*> v2 <*> v3 <*> v4

instance Substable Value where
  fv (VLam x v) = Set.delete x (fv v)
  fv VStar = Set.empty
  fv (VPi x v' v) = fv v' `Set.union` Set.delete x (fv v)
  fv (VNeutral n) = fv n
  fv VNat = Set.empty
  fv VZero = Set.empty
  fv (VSucc v) = fv v

  subst x v (VLam y t) =
    if x == y
      then return $ VLam y t
      else let y' = genName v y in VLam y' <$> (rename y y' t >>= subst x v)
  subst x v VStar = return VStar
  subst x v (VPi y ty' ty) =
    let y' = genName ty y
     in VPi y' <$> subst x v ty' <*> (rename y y' ty >>= subst x v)
  subst x v (VNeutral n) = subst x v n
  subst x v VNat = return VNat
  subst x v VZero = return VZero
  subst x v (VSucc v') = VSucc <$> subst x v v'

instance Substable Neutral where
  fv (NFree x) = Set.singleton x
  fv (NApp n v) = fv n `Set.union` fv v
  fv (NNatElim v1 v2 v3 n) = fv v1 `Set.union` fv v2 `Set.union` fv v3 `Set.union` fv n

  subst x v (NFree y) = return $ if x == y then v else VNeutral (NFree y)
  subst x v (NApp n v') = subst x v n `vappM` subst x v v'
  subst x v (NNatElim m mz ms k) = evalNatM (subst x v m) (subst x v mz) (subst x v ms) (subst x v k)

class Evalable a where
  eval :: a -> Result Value

instance Evalable ITerm where
  eval (t ::: _) = eval t
  eval Star = return VStar
  eval (Pi x ty t) = VPi x <$> eval ty <*> eval t
  eval (Var x) = return $ vfree x
  eval (t1 :@: t2) = eval t1 `vappM` eval t2
  eval Nat = return VNat
  eval Zero = return VZero
  eval (Succ t) = VSucc <$> eval t
  eval (NatElim m mz ms k) = evalNatM (eval m) (eval mz) (eval ms) (eval k)

instance Evalable CTerm where
  eval (Inf t) = eval t
  eval (Lam x t) = VLam x <$> eval t

-- type check & inference
type Type = Value

type TI = StateT (M.Map Id Type) Result

typeInfer :: ITerm -> TI Type
typeInfer (t ::: ty) = do
  typeCheck ty VStar
  ty' <- lift $ eval ty
  typeCheck t ty'
  return ty'
typeInfer Star = return VStar
typeInfer (Pi x ty t) = do
  typeCheck ty VStar
  ty' <- lift $ eval ty
  withStateT (M.insert x ty') $ do
    typeCheck t VStar
    return VStar
typeInfer (Var x) = do
  ctx <- get
  case M.lookup x ctx of
    Nothing -> throwError $ "unbound variable: " ++ x
    Just ty -> return ty
typeInfer t@(t1 :@: t2) = do
  ty1 <- typeInfer t1
  case ty1 of
    VPi x ty ty' -> do
      typeCheck t2 ty
      v2 <- lift $ eval t2
      lift $ subst x v2 ty'
    _ -> throwError $ "illegal application: " ++ show t
typeInfer Nat = return VStar
typeInfer Zero = return VNat
typeInfer (Succ t) = do
  typeCheck t VNat
  return VNat
typeInfer (NatElim m mz ms k) = do
  typeCheck m (VPi "a" VNat VStar)

  vm <- lift $ eval m

  tyMz <- lift $ vm `vapp` VZero
  typeCheck mz tyMz

  tyMs <- lift $ do
    vml <- vm `vapp` vfree "l"
    vmsl <- vm `vapp` VSucc (vfree "l")
    return $ VPi "l" VNat (VPi "mk" vml vmsl)
  typeCheck ms tyMs

  typeCheck k VNat

  vk <- lift $ eval k
  lift $ vm `vapp` vk

typeCheck :: CTerm -> Type -> TI ()
typeCheck (Inf t) ty = do
  ty' <- typeInfer t
  unless (ty == ty') $ throwError $ "type mismatch: " ++ show ty ++ " vs " ++ show ty'
typeCheck (Lam x t) (VPi x' ty ty') = do
  ty'' <- lift $ rename x' x ty'
  withStateT (M.insert x ty) $ typeCheck t ty''
typeCheck t ty = throwError $ "type mismatch: " ++ show t ++ " vs " ++ show ty

runTI :: TI a -> Either String a
runTI tc = evalStateT tc M.empty
