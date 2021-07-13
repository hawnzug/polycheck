module Test.PolyCheck.TH.Predicate where

import Data.Function
import Data.Functor
import Data.Traversable (for)
import qualified Data.Map.Strict as Map
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Datatype

import Test.PolyCheck.TH.State
import Test.PolyCheck.TH.TypeExp (flattenApps)

tvOccurs :: Name -> Type -> Q Bool
tvOccurs a = go where
  go = \case
    VarT b -> pure $ a == b
    ConT b -> pure False
    TupleT 0 -> pure False
    AppT (AppT ArrowT arg) ret ->
      (||) <$> go arg <*> go ret
    t@(AppT _ _) -> do
      let (constr, args) = flattenApps t
      case constr of
        TupleT n -> or <$> traverse go args
        ListT -> let [arg] = args in go arg
        ConT datatypeName -> tvOccursCon a (datatypeName, args)
        _ -> fail "Not supported"
    _ -> fail "Not supported"

tvOccursCon :: Name -> (Name, [Type]) -> Q Bool
tvOccursCon a (datatypeName, args) = do
  info <- reifyDT datatypeName
  let vars = info & datatypeVars <&> tvName
  let cons = info & datatypeCons
  varOccurs <- getTvOccur datatypeName >>= \case
    Just vs -> pure vs
    Nothing -> do
      putTvOccur datatypeName (vars $> False)
      varOccurs <- for vars $ \var ->
        anyM (tvOccurs var) (concatMap constructorFields cons)
      putTvOccur datatypeName varOccurs
      pure varOccurs
  tvs <- traverse (tvOccurs a) args
  pure $ or $ zipWith (&&) varOccurs tvs
  where anyM f xs = or <$> traverse f xs

isEmpty :: Type -> Q Bool
isEmpty = go where
  go = \case
    VarT _ -> fail "Cannot determine the emptiness for open types"
    ConT name -> isEmptyCon (name, [])
    TupleT 0 -> pure False
    AppT (AppT ArrowT arg) ret -> do
      e1 <- go arg
      e2 <- go ret
      pure (not e1 && e2)
    t@(AppT _ _) -> do
      let (constr, args) = flattenApps t
      case constr of
        TupleT n -> or <$> traverse go args
        ListT -> pure False
        ConT datatypeName -> isEmptyCon (datatypeName, args)
        _ -> fail "Not supported"
    _ -> fail "Not supported"

isEmptyCon :: (Name, [Type]) -> Q Bool
isEmptyCon (datatypeName, args) = do
  info <- reifyDT datatypeName
  let vars = info & datatypeVars <&> tvName
  let cons = info & datatypeCons
  let subst = applySubstitution $ Map.fromList $ zip vars args
  getEmptiness datatypeName >>= \case
    Just e -> pure e
    Nothing -> do
      putEmptiness datatypeName True
      e <- allM (anyM isEmpty . (subst . constructorFields)) cons
      putEmptiness datatypeName e
      pure e
  where
    anyM f xs = or <$> traverse f xs
    allM f xs = and <$> traverse f xs

tvStrictlyPositive :: Name -> Type -> Q Bool
tvStrictlyPositive a = go where
  go = \case
    VarT _ -> pure True
    ConT _ -> pure True
    TupleT 0 -> pure True
    AppT (AppT ArrowT arg) ret -> do
      b1 <- tvOccurs a arg
      b2 <- go ret
      pure $ not b1 && b2
    t@(AppT _ _) -> do
      let (constr, args) = flattenApps t
      case constr of
        TupleT n -> and <$> traverse go args
        ListT -> let [arg] = args in go arg
        ConT datatypeName -> tvStrictlyPositiveCon a (datatypeName, args)
        _ -> fail "Not supported"
    _ -> fail "Not supported"

tvStrictlyPositiveCon :: Name -> (Name, [Type]) -> Q Bool
tvStrictlyPositiveCon a (datatypeName, args) = do
  info <- reifyDT datatypeName
  let vars = info & datatypeVars <&> tvName
  let cons = info & datatypeCons
  varOccurs <- getTvOccur datatypeName >>= \case
    Just vs -> pure vs
    Nothing -> do
      putTvOccur datatypeName (vars $> False)
      varOccurs <- for vars $ \var ->
        anyM (tvOccurs var) (concatMap constructorFields cons)
      putTvOccur datatypeName varOccurs
      pure varOccurs
  varSP <- getTvSP datatypeName >>= \case
    Just vs -> pure vs
    Nothing -> do
      putTvSP datatypeName (vars $> True)
      varSP <- for vars $ \var ->
        allM (tvStrictlyPositive var) (concatMap constructorFields cons)
      putTvSP datatypeName varSP
      pure varSP
  let f (b2, b4, arg) = do
        b1 <- tvOccurs a arg
        b3 <- tvStrictlyPositive a arg
        pure $ not b1 || not b2 || b3 && b4
  allM f (zip3 varOccurs varSP args)
  where allM f xs = and <$> traverse f xs
        anyM f xs = or <$> traverse f xs

resTypeRequired :: [Name] -> (Name, [Type]) -> Q Bool
resTypeRequired as (datatypeName, args) = flip anyM as $ \a -> do
  info <- reifyDT datatypeName
  let vars = info & datatypeVars <&> tvName
  let cons = info & datatypeCons
  let f (var, arg) = do
        b1 <- tvOccurs a arg
        b2 <- allM (tvStrictlyPositive var) (concatMap constructorFields cons)
        pure $ b1 && not b2
  anyM f (zip vars args)
  where allM f xs = and <$> traverse f xs
        anyM f xs = or <$> traverse f xs
