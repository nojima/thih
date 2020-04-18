{-# LANGUAGE OverloadedStrings #-}
module Typing where

import           Control.Monad (msum)
import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Text as T
import           Data.Text (Text)

type Id = Text

enumId :: Int -> Id
enumId n = "v" <> T.pack (show n)

-- カインド
data Kind
    = Star
    | KFun Kind Kind
    deriving (Show, Eq)

-- 型
data Type
    = TVariable Variable
    | TConstant Constant
    | TApply Type Type
    | TGeneric Int
    deriving (Show, Eq)

-- 型変数
data Variable = Variable Id Kind
    deriving (Show)

instance Eq Variable where
    (Variable id1 _) == (Variable id2 _) =
        id1 == id2

instance Ord Variable where
    compare (Variable id1 _) (Variable id2 _) =
        compare id1 id2

-- 定数型 (型引数を取らない型)
data Constant = Constant Id Kind
    deriving (Show, Eq)

-- プリミティブ型
tUnit    = TConstant (Constant "()"      Star)
tChar    = TConstant (Constant "Char"    Star)
tInt     = TConstant (Constant "Int"     Star)
tInteger = TConstant (Constant "Integer" Star)
tFloat   = TConstant (Constant "Float"   Star)
tDouble  = TConstant (Constant "Double"  Star)
tList    = TConstant (Constant "[]"   (KFun Star Star))
tArrow   = TConstant (Constant "(->)" (KFun Star (KFun Star Star)))
tTuple2  = TConstant (Constant "(,)"  (KFun Star (KFun Star Star)))

-- 便利関数
infixr 4 `fn`
fn :: Type -> Type -> Type
a `fn` b =
    (tArrow `TApply` a) `TApply` b

list :: Type -> Type
list t =
    TApply tList t

pair :: Type -> Type -> Type
pair a b =
    (tTuple2 `TApply` a) `TApply` b

-- kind 関数
class HasKind t where
    kind :: t -> Kind

instance HasKind Variable where
    kind (Variable _ k) = k

instance HasKind Constant where
    kind (Constant _ k) = k

instance HasKind Type where
    kind type_ =
        case type_ of
            TVariable u  ->
                kind u
            TConstant tc ->
                kind tc
            TApply t _ ->
                case kind t of
                    KFun _ k -> k
                    _ -> error $ "kind is not defined for TApply "
                              ++ "where the kind of argument is not KFun: "
                              ++ show type_
            TGeneric _ ->
                error $ "kind is not defined for TGeneric: " ++ show type_

-- 型代入
type Subst = Map Variable Type

nullSubst :: Subst
nullSubst =
    Map.empty

(+->) :: Variable -> Type -> Subst
u +-> t =
    Map.singleton u t

class Types t where
    apply :: Subst -> t -> t
    typeVariables :: t -> Set Variable

instance Types Type where
    apply subst type_ =
        case type_ of
            TVariable u ->
                case Map.lookup u subst of
                    Just t  -> t
                    Nothing -> TVariable u
            TApply lhs rhs ->
                apply subst lhs `TApply` apply subst rhs
            _ ->
                type_

    typeVariables type_ =
        case type_ of
            TVariable u ->
                Set.singleton u
            TApply lhs rhs ->
                typeVariables lhs `Set.union` typeVariables rhs
            _ ->
                Set.empty

instance Types a => Types [a] where
    apply =
        map . apply

    typeVariables =
        Set.unions . map typeVariables

infixr 4 @@
(@@) :: Subst -> Subst -> Subst
s1 @@ s2 =
    Map.map (apply s1) s2 `Map.union` s1

merge :: MonadFail m => Subst -> Subst -> m Subst
merge s1 s2 =
    if all mapsToSameType intersection then
        return $ Map.union s1 s2
    else
        fail $ "cannot merge s1 and s2: s1="
            ++ show s1 ++ ", s2=" ++ show s2
  where
    intersection =
        Map.keys $ Map.intersection s1 s2
    mapsToSameType v =
        apply s1 (TVariable v) == apply s2 (TVariable v)
