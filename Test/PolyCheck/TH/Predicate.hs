{-# LANGUAGE MagicHash #-}
module Test.PolyCheck.TH.Predicate where

import qualified Data.List as List
import qualified Data.Either as Either
import Data.Function
import Data.Functor
import Data.Traversable (for)
import qualified Data.Map.Strict as Map
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Datatype
import GHC.Exts

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

isEmpty :: Type -> Q Emptiness
isEmpty (VarT _) = fail "Cannot determine the emptiness for open types"
isEmpty (ConT name) =
  if name == ''Integer
  then NonEmpty <$> [| 0 |]
  else reify name >>= \case
  PrimTyConI{} ->
    if name == ''Int#
    then NonEmpty <$> [| 0# |]
    else if name == ''Word#
    then NonEmpty <$> [| 0## |]
    else if name == ''Float#
    then NonEmpty <$> [| 0.0# |]
    else if name == ''Double#
    then NonEmpty <$> [| 0.00## |]
    else if name == ''Char#
    then NonEmpty <$> [| 'a'# |]
    else fail $ "Unsupported primitive type" <> pprint name <> pprint ''Int
  _ -> isEmptyCon (name, [])
isEmpty (TupleT 0) = NonEmpty <$> [| () |]
isEmpty (AppT (AppT ArrowT arg) ret) = do
  isEmpty arg >>= \case
    Empty e1 -> NonEmpty <$> [| absurd . $(pure e1) |]
    NonEmpty e1 -> isEmpty ret >>= \case
      NonEmpty e2 -> NonEmpty <$> [| const $(pure e2) |]
      Empty e2 -> Empty <$> [| \f -> $(pure e2) (f $(pure e1)) |]
isEmpty t@(AppT _ _) = do
  let (constr, args) = flattenApps t
  case constr of
    TupleT n -> do
      emps <- traverse isEmpty args
      case List.findIndex emptyB emps of
        Just i -> do
          x <- newName "x"
          let pat = tupP [if j == i then varP x else wildP | j <- [0..n-1]]
          let e = (\(Empty e) -> pure e) (emps !! i)
          Empty <$> [| \ $pat -> $e $(varE x) |]
        Nothing -> pure $ NonEmpty $ TupE $
          fmap (\(NonEmpty e) -> Just e) emps
    ListT -> NonEmpty <$> [| [] |]
    ConT datatypeName -> isEmptyCon (datatypeName, args)
    _ -> fail "Not supported"
isEmpty _ = fail "Not supported"

isEmptyCon :: (Name, [Type]) -> Q Emptiness
isEmptyCon (datatypeName, args) = do
  info <- reifyDT datatypeName
  let vars = info & datatypeVars <&> tvName
  let cons = info & datatypeCons
  let subst = applySubstitution $ Map.fromList $ zip vars args
  getEmptiness datatypeName >>= \case
    Just f -> pure $ Empty $ VarE f
    Nothing -> do
      f <- newName "f"
      putEmptiness datatypeName f
      emp <- checkCons f (subst $ datatypeCons info)
      deleteEmptiness datatypeName
      pure emp
  where
    checkCons :: Name -> [ConstructorInfo] -> Q Emptiness
    checkCons name cons = do
      emps <- traverse checkCon cons
      case List.find Either.isRight emps of
        Just e -> pure $ NonEmpty $ case e of Right x -> x
        Nothing -> do
          let matches = fmap (\(Left m) -> m) emps
          let dec = ValD (VarP name) (NormalB $ LamCaseE matches) []
          pure $ Empty $ LetE [dec] (VarE name)
    checkCon :: ConstructorInfo -> Q (Either Match Exp)
    checkCon con = do
      let name = constructorName con
      let fields = constructorFields con
      let n = length fields
      emps <- traverse isEmpty fields
      case List.findIndex emptyB emps of
        Just i -> do
          x <- newName "x"
          let pats = [if j == i then VarP x else WildP | j <- [0..n-1]]
          let e = case emps !! i of Empty e -> e
          pure $ Left $ Match (ConP name pats) (NormalB $ AppE e (VarE x)) []
          -- [| \ $(conP name pat) -> $e $(varE x) |]
        Nothing -> pure $ Right $
          foldl AppE (ConE name) $ fmap (\(NonEmpty e) -> e) emps
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
