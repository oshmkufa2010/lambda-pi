module STLC where

import Control.Monad (when)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.State (MonadState (get, put), State, StateT, evalStateT, withStateT)
import qualified Data.Map as M
import qualified Data.Set as Set

-- type rules

infixr 9 :=>:

infixl 2 :@:

infix 1 :::

type Id = String

data Kind = Star deriving (Show, Eq)

data Type
  = TFree Id
  | Type :=>: Type
  deriving (Show, Eq)

data Info
  = HasKind Kind
  | HasType Type
  deriving (Show, Eq)

type Context = M.Map Id Info

data InfTerm
  = CheTerm ::: Type
  | Var Id
  | InfTerm :@: CheTerm
  deriving (Show, Eq)

data CheTerm
  = Inf InfTerm
  | Lam Id CheTerm
  deriving (Show, Eq)

type TC = StateT Context (Either String)

kind :: Type -> Kind -> TC ()
kind (TFree x) Star = do
  ctx <- get
  case M.lookup x ctx of
    Just (HasKind Star) -> return ()
    _ -> throwError $ "unknown type: " ++ x
kind (a :=>: b) Star = do
  kind a Star
  kind b Star

typeOfInf :: InfTerm -> TC Type
typeOfInf (t ::: ty) = do
  kind ty Star
  typeOfChe t ty
  return ty
typeOfInf (Var x) = do
  ctx <- get
  case M.lookup x ctx of
    Just (HasType ty) -> return ty
    _ -> throwError $ "unbound variable: " ++ x
typeOfInf t@(t1 :@: t2) = do
  ty1 <- typeOfInf t1
  case ty1 of
    a :=>: b -> typeOfChe t2 a >> return b
    _ -> throwError $ "illegal application on " ++ show t

typeOfChe :: CheTerm -> Type -> TC ()
typeOfChe t'@(Inf t) ty = do
  ty' <- typeOfInf t
  when (ty /= ty') $ throwError $ "type mismatch on " ++ show t' ++ " : expected " ++ show ty ++ ", bug got " ++ show ty'
typeOfChe (Lam x t) (ty1 :=>: ty2) = withStateT (M.insert x (HasType ty1)) (typeOfChe t ty2)
typeOfChe t@(Lam _ _) ty = throwError $ "type mismatch on " ++ show t ++ " : expected a function type, bug got " ++ show ty

-- eval

data Term = TmVar Id | TmApp Term Term | TmLam Id Term

instance Show Term where
  show (TmVar x) = x
  show (TmApp (TmVar x1) (TmVar x2)) = x1 ++ " " ++ x2
  show (TmApp (TmVar x1) t2) = x1 ++ " (" ++ show t2 ++ ")"
  show (TmApp t1 (TmVar x2)) = "(" ++ show t1 ++ ") " ++ x2
  show (TmApp t1 t2) = "(" ++ show t1 ++ ") (" ++ show t2 ++ ")"
  -- show (TmLam x (TmVar y)) = "λ" ++ x ++ "." ++
  show (TmLam x t) = "λ" ++ x ++ ". " ++ show t

eraseInf :: InfTerm -> Term
eraseInf (t ::: _) = eraseChe t
eraseInf (Var x) = TmVar x
eraseInf (t1 :@: t2) = TmApp (eraseInf t1) (eraseChe t2)

eraseChe :: CheTerm -> Term
eraseChe (Inf t) = eraseInf t
eraseChe (Lam x t) = TmLam x (eraseChe t)

freeVars :: Term -> Set.Set Id
freeVars (TmVar x) = Set.singleton x
freeVars (TmApp t1 t2) = freeVars t1 `Set.union` freeVars t2
freeVars (TmLam x t) = Set.delete x (freeVars t)

genName :: Set.Set Id -> Id -> Id
genName freeVars x = case ns of
  0 -> x
  _ -> x ++ show ns
  where
    ns = length $ takeWhile (`Set.member` freeVars) $ x : map ((x ++) . show) [1 ..]

subst :: Id -> Term -> Term -> Term
subst x v (TmVar y) = if x == y then v else TmVar y
subst x v (TmApp t1 t2) = TmApp (subst x v t1) (subst x v t2)
subst x v (TmLam y t) =
  let y' = genName (freeVars v) y
    in TmLam y' (subst x v (subst y (TmVar y') t))

eval :: Term -> Term
eval t@(TmVar x) = t
eval (TmLam x t) = TmLam x (eval t)
eval (TmApp t1 t2) =
  let v1 = eval t1
   in let v2 = eval t2
       in case v1 of
            TmLam x t -> eval (subst x v2 t)
            _ -> TmApp v1 v2

data Value = VLam Id Value | VNeutral Neutral

data Neutral = NFree Id | NApp Neutral Value

value2Term :: Value -> Term
value2Term (VLam x v)= TmLam x (value2Term v)
value2Term (VNeutral n) = neutral2Term n

neutral2Term :: Neutral -> Term
neutral2Term (NFree x) = TmVar x
neutral2Term (NApp n v) = TmApp (neutral2Term n) (value2Term v)

instance Show Value where
  show = show . value2Term

instance Show Neutral where
  show = show . neutral2Term

freeVarsOfValue :: Value -> Set.Set Id
freeVarsOfValue (VLam x v) = Set.delete x (freeVarsOfValue v)
freeVarsOfValue (VNeutral n) = freeVarsOfNeutral n

freeVarsOfNeutral :: Neutral -> Set.Set Id
freeVarsOfNeutral (NFree x) = Set.singleton x
freeVarsOfNeutral (NApp n v) = freeVarsOfNeutral n `Set.union` freeVarsOfValue v

substValue :: Id -> Value -> Value -> Value
substValue x v (VLam y t) = let y' = genName (freeVarsOfValue v) y in VLam y' (substValue x v (substValue y (VNeutral (NFree y')) t))
substValue x v (VNeutral n) = substNeutral x v n

substNeutral :: Id -> Value -> Neutral -> Value
substNeutral x v (NFree y) = if x == y then v else VNeutral (NFree y)
substNeutral x v (NApp n v') =
  let v2 = substValue x v v'
   in case substNeutral x v n of
        VLam y t -> substValue y v2 t
        VNeutral n' -> VNeutral (NApp n' v2)

eval' :: Term -> Value
eval' t@(TmVar x) = VNeutral (NFree x)
eval' (TmLam x t) = VLam x (eval' t)
eval' (TmApp t1 t2) =
  let v1 = eval' t1
   in let v2 = eval' t2
       in case v1 of
            VLam x v -> substValue x v2 v
            VNeutral n -> VNeutral (NApp n v2)

-- test case

natType :: Type
natType = (TFree "A" :=>: TFree "A") :=>: TFree "A" :=>: TFree "A"

cheVar :: Id -> CheTerm
cheVar = Inf . Var

zero :: InfTerm
zero = Lam "s" (Lam "z" (Inf (Var "z"))) ::: natType

suc :: InfTerm
suc =
  Lam
    "n"
    ( Lam
        "s"
        ( Lam
            "z"
            ( Inf (Var "s" :@: cheVar "n" :@: cheVar "s" :@: cheVar "z")
            )
        )
    )
    ::: natType :=>: natType

one :: InfTerm
one = suc :@: Inf zero

plus :: InfTerm
plus = Lam "m" (Lam "n" (Lam "s" (Lam "z" (Inf (Var "m" :@: cheVar "s" :@: Inf (Var "n" :@: cheVar "s" :@: cheVar "z")))))) ::: natType :=>: natType :=>: natType
