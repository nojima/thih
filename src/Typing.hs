{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
module Typing where

import           Control.Monad ((>=>))
import qualified Data.Maybe as Maybe
import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import qualified Data.Set as Set
import           Data.Set (Set)
import qualified Data.Text as T
import           Data.Text (Text)

type Id = Text

enumId :: Int -> Id
enumId n = "v" <> T.pack (show n)

-- エラー
newtype TypeError = TypeError Text
    deriving (Show, Eq)

type Result a = Either TypeError a

typeError :: Text -> Result a
typeError errorMessage =
    Left (TypeError errorMessage)

isDefined :: Result a -> Bool
isDefined (Right _) = True
isDefined (Left  _) = False

panic :: Text -> a
panic errorMessage =
    error (T.unpack errorMessage)

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
                    _ -> panic $ "kind is not defined for TApply "
                              <> "where the kind of argument is not KFun: "
                              <> T.pack (show type_)
            TGeneric _ ->
                panic $ "kind is not defined for TGeneric: " <> T.pack (show type_)

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

merge :: Subst -> Subst -> Result Subst
merge s1 s2 =
    if all mapsToSameType intersection then
        return (Map.union s1 s2)
    else
        typeError
            $ "cannot merge s1 and s2: s1="
            <> T.pack (show s1)
            <> ", s2="
            <> T.pack (show s2)
  where
    intersection =
        Map.keys (Map.intersection s1 s2)
    mapsToSameType v =
        apply s1 (TVariable v) == apply s2 (TVariable v)

-- Unification
mgu :: Type -> Type -> Result Subst
mgu type1 type2 =
    case (type1, type2) of
        (TApply lhs1 rhs1, TApply lhs2 rhs2) -> do
            subst1 <- mgu lhs1 lhs2
            subst2 <- mgu (apply subst1 rhs1) (apply subst1 rhs2)
            return (subst2 @@ subst1)

        (TVariable u, t) ->
            bindVariable u t

        (t, TVariable u) ->
            bindVariable u t

        (TConstant tc1, TConstant tc2) | tc1 == tc2 ->
            return nullSubst

        _ ->
            typeError
                $ "type1 and type2 cannot be unified: type1="
                <> T.pack (show type1)
                <> ", type2="
                <> T.pack (show type2)

bindVariable :: Variable -> Type -> Result Subst
bindVariable u t
    | t == TVariable u               = return nullSubst
    | u `Set.member` typeVariables t = typeError "occurs check fails"
    | kind u /= kind t               = typeError "kinds do not match"
    | otherwise                      = return (u +-> t)

match :: Type -> Type -> Result Subst
match type1 type2 =
    case (type1, type2) of
        (TApply lhs1 rhs1, TApply lhs2 rhs2) -> do
            subst1 <- match lhs1 lhs2
            subst2 <- match rhs1 rhs2
            merge subst1 subst2

        (TVariable u, t) | kind u == kind t ->
            return (u +-> t)

        (TConstant tc1, TConstant tc2) | tc1 == tc2 ->
            return nullSubst

        _ ->
            typeError
                $ "type1 and type2 do not match: type1="
                <> T.pack (show type1)
                <> ", type2="
                <> T.pack (show type2)

-- 型クラス


data Qualified t =
    [Predicate] :=> t    -- ps :=> t における ps を "context" と呼び、t を "head" と呼ぶ
    deriving (Show, Eq)

data Predicate =
    IsIn Id Type
    deriving (Show, Eq)

instance Types t => Types (Qualified t) where
    apply subst (predicates :=> type_) =
        apply subst predicates :=> apply subst type_

    typeVariables (predicates :=> type_) =
        typeVariables predicates `Set.union` typeVariables type_

instance Types Predicate where
    apply subst (IsIn ident type_) =
        IsIn ident (apply subst type_)

    typeVariables (IsIn _ type_) =
        typeVariables type_

mguPred :: Predicate -> Predicate -> Result Subst
mguPred = lift mgu

matchPred :: Predicate -> Predicate -> Result Subst
matchPred = lift match

lift :: (Type -> Type -> Result a) -> Predicate -> Predicate -> Result a
lift f (IsIn ident1 type1) (IsIn ident2 type2)
    | ident1 == ident2 = f type1 type2
    | otherwise        = typeError "classes differ"

type Instance = Qualified Predicate

data Class = Class
    { _superClasses :: [Id]       -- name of each superclass
    , _instances    :: [Instance] -- an entry for each instance declaration
    }
    deriving (Show, Eq)

-- クラス環境
data ClassEnv = ClassEnv
    { _classes  :: Map Id Class
    , _defaults :: [Type]
    }

super :: ClassEnv -> Id -> [Id]
super classEnv ident =
    case Map.lookup ident (_classes classEnv) of
        Just Class{_superClasses} ->
            _superClasses
        _ ->
            panic $ "`" <> ident <> "` is not a class"

instances :: ClassEnv -> Id -> [Instance]
instances classEnv className =
    case Map.lookup className (_classes classEnv) of
        Just Class{_instances} ->
            _instances
        _ ->
            panic $ "`" <> className <> "` is not a class"

modify :: ClassEnv -> Id -> Class -> ClassEnv
modify classEnv name class_ =
    classEnv{_classes = Map.insert name class_ (_classes classEnv)}

initialClassEnv :: ClassEnv
initialClassEnv =
    ClassEnv
        { _classes  = Map.empty
        , _defaults = [tInteger, tDouble]
        }

type EnvTransformer = ClassEnv -> Result ClassEnv

addClass :: Id -> [Id] -> EnvTransformer
addClass className superClasses classEnv@ClassEnv{_classes}
    | defined className =
        typeError ("class `" <> className <> "` already defined")
    | not (all defined superClasses) =
        typeError "superclass not defined"
    | otherwise =
        let newClass = Class superClasses [] in
        return (modify classEnv className newClass)
  where
    defined name =
        Maybe.isJust (Map.lookup name _classes)

addPreludeClasses :: EnvTransformer
addPreludeClasses =
    addCoreClasses >=> addNumClasses

addCoreClasses :: EnvTransformer
addCoreClasses =
    addClass "Eq" []
    >=> addClass "Ord" ["Eq"]
    >=> addClass "Show" []
    >=> addClass "Read" []
    >=> addClass "Bounded" []
    >=> addClass "Enum" []
    >=> addClass "Functor" []
    >=> addClass "Monad" []

addNumClasses :: EnvTransformer
addNumClasses =
    addClass "Num" ["Eq", "Show"]
    >=> addClass "Real" ["Num", "Ord"]
    >=> addClass "Fractional" ["Num"]
    >=> addClass "Integral" ["Real", "Enum"]
    >=> addClass "RealFrac" ["Real", "Fractional"]
    >=> addClass "Floating" ["Fractional"]
    >=> addClass "RealFloat" ["RealFrac", "Floating"]

addInstance :: [Predicate] -> Predicate -> EnvTransformer
addInstance context head_@(IsIn className _) classEnv@ClassEnv{_classes}
    | not (defined className) =
        typeError ("class `" <> className <> "` is not defined")
    | any (overlap head_) heads =
        typeError "overlapping instance"
    | otherwise =
        return (modify classEnv className newClass)
  where
    defined name =
        Maybe.isJust (Map.lookup name _classes)

    insts =
        instances classEnv className

    heads =
        map (\(_ :=> q) -> q) insts

    newClass =
        Class (super classEnv className) ((context :=> head_) : insts)

-- two instances for a class are said to overlap if there is some predicate that
-- is a substition instance of the heads of both instance declarations
overlap :: Predicate -> Predicate -> Bool
overlap pred1 pred2 =
    isDefined (mguPred pred1 pred2)
