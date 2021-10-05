{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Test.PolyCheck.TH where

import Test.PolyCheck.TH.State
import Test.PolyCheck.TH.TypeExp
import Test.PolyCheck.TH.Predicate

import Data.List (intersperse, zip4, unzip4)
import Data.Functor
import Data.Function
import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Void (Void, absurd)
import Data.Traversable (for)
import GHC.Generics (Generic)
import Test.SmallCheck
import Test.SmallCheck.Series

-- | Monomorphise a polymorphic function so that it can be tested by QuickCheck.
--
-- > prop :: Eq b => (a -> b) -> [a] -> Bool
-- > $(monomorphic prop)
--
-- A monomorphized function 'prop_mono' will be generated, and can be use in
-- @quickCheck prop_mono@.
monomorphic :: Name -> Q [Dec]
monomorphic name = do
  (vars, params, returnType) <- reifyType name >>= resolveTypeSynonyms >>= destructFnType
  qStateInit (last vars) nameStr
  let t = mkTupleT params
  let (logTypeNames, logConNames, skelConNames, fillNames) = unzip4 $ vars <&> \var ->
        let make s = mkName $ s <> nameStr <> nameBase var in
        (make "TestLog", make "TestLogCon", make "TestSkelCon", make "testfill")
  genLogs t vars logTypeNames logConNames skelConNames
  substLogDecs vars logTypeNames
  let subst = applySubstitution $ Map.fromList $ zip vars (ConT <$> logTypeNames)
  genFill t vars fillNames logConNames
  genMonoType (length params) monoTypeName monoTypeConName fillNames (subst t)
  genMonoFun (length params) name monoName monoTypeName monoTypeConName (subst returnType)
  concat <$> sequence [getLogDecs, getFillDecs, getDecs]
  where
    -- reifyType for template-haskell >= 2.11 <= 2.15
    reifyType name = reify name <&> \(VarI _ t _) -> t
    nameStr = nameBase name
    monoName = mkName $ nameStr <> "_mono"
    monoTypeName = mkName $ "Mono" <> nameStr
    monoTypeConName = mkName $ "MonoC" <> nameStr

genLogs :: Type -> [Name] -> [Name] -> [Name] -> [Name] -> Q ()
genLogs t vars typeNames logConNames skelConNames =
  mapM_ go $ zip4 vars typeNames logConNames skelConNames
  where
    go (a, typeName, logConName, skelConName) = do
      log <- logt a t
      putLogDec (a, a, []) $
          DataD [] typeName [] Nothing
          [mkConD logConName [log], mkConD skelConName []]
          [DerivClause Nothing [ConT ''Eq, ConT ''Show, ConT ''Generic]]
      f <- newName "f"
      x <- newName "x"
      putDecs =<<
        [d| instance Monad m => CoSerial m $(conT typeName) -- where
              -- coseries rs = newtypeAlts rs >>- \ $(varP f) ->
              --   pure $ \ $(conP logConName [varP x]) -> $(varE f) $(varE x)
            instance Monad m => Serial m $(conT typeName) where
              series = cons0 $(conE skelConName)
          |]

genFill :: Type -> [Name] -> [Name] -> [Name] -> Q ()
genFill t vars fillNames conNames =
  mapM_ go $ zip3 vars fillNames conNames
  where
    go (a, fillName, conName) = do
      x <- newName "e"
      fillDec <-
        funD fillName $
        [clause [varP x] (normalB $ fill a t (varE x) (conE conName)) []]
      putFillDec (a, fillName, []) fillDec

genMonoType :: Int -> Name -> Name -> [Name] -> Type -> Q ()
genMonoType numArgs monoTypeName monoTypeConName fillNames t = do
  x <- newName "x"
  instDec <-
    [d|
     instance Monad m => Serial m $(conT monoTypeName) where
       series = ($fills :: $(pure t) -> $(conT monoTypeName)) <$> series
     instance Show $(conT monoTypeName) where
       show $(conP monoTypeConName [varP x]) = $(showMono x)
     |]
  putDecs $ monoTypeDec : instDec
  where
    monoTypeDec = NewtypeD [] monoTypeName [] Nothing
      (mkConD monoTypeConName [t]) []
    fills = foldl (\f g -> [| $f . $g |])
      (conE monoTypeConName) (varE <$> reverse fillNames)
    showMono x = case numArgs of
      1 -> [| show $(varE x) |]
      n -> let xs = [0..n-1] <&> \i -> [| show ($(proji n i) $(varE x)) |] in
           [| concat $ intersperse "\n" $(listE xs) |]

genMonoFun :: Int -> Name -> Name -> Name -> Name -> Type -> Q ()
genMonoFun numArgs func monoName monoTypeName monoTypeConName returnType = do
  monoSig <- sigD monoName
    [t| $(conT monoTypeName) -> $(pure returnType) |]
  x <- newName "x"
  let body = case numArgs of
        1 -> [| $(varE func) $(varE x) |]
        n -> foldl appE (varE func) $ [0..n-1] <&>
             \i -> [| $(proji n i) $(varE x) |]
  monoDec <- funD monoName
    [clause [conP monoTypeConName [varP x]] (normalB body) []]
  putDecs [monoSig, monoDec]

-- | Calculate the log type of @t@ w.r.t. @a@
logt :: Name -> Type -> Q Type
logt a (VarT b) | a == b = [t| () |]
logt a (VarT b) = [t| Void |]
logt a (ConT b) = [t| Void |]
logt a (TupleT 0) = [t| Void |]
logt a t@(AppT (AppT ArrowT _) _) = do
  let (args, ret) = flattenArrows t
  logret <- logt a ret
  pure $ mkTupleT (args ++ [logret])
logt a t@(AppT _ _) = do
  let (constr, params) = flattenApps t
  case constr of
    TupleT _ -> mkEithersT <$> traverse (logt a) params
    ListT -> let [param] = params in [t| ListLog $(logt a param) |]
    ConT typeName -> logCon a (typeName, params)
    _ -> fail "Not supported"
logt _ _ = fail "Not supported"

logCon :: Name -> (Name, [Type]) -> Q Type
logCon a (typeName, args) =
  getLogType (a, typeName, args) >>= maybe new pure
  where
    new = do
      info <- reifyDT typeName
      logTypeName <- mkLogTypeName (a, typeName, args)
      logCons <-
        let vars = tvName <$> datatypeVars info in
        let subst = applySubstitution $ Map.fromList $ zip vars args in
        forM (info & datatypeCons & subst) $ \con -> do
          logFields <- traverse (logt a) (constructorFields con)
          name <- newUniqueName $ nameBase (constructorName con) <> "LogC"
          pure $ mkConD name [mkEithersT logFields]
      putLogDec (a, typeName, args) $
        DataD [] logTypeName [] Nothing logCons
        [DerivClause Nothing (ConT <$> [''Eq, ''Show, ''Generic])]
      putDecs =<< [d| instance Monad m => CoSerial m $(conT logTypeName) |]
      conT logTypeName

fill :: Name -- ^ The type variable a
     -> Type -- ^ The type t
     -> Q Exp -- ^ The skeleton e
     -> Q Exp -- ^ The label prefix f
     -> Q Exp
fill a (VarT b) e f | a == b = [| $f () |]
fill a (VarT b) e f = e
fill a (ConT c) e f = e
fill a (TupleT 0) e f = [| () |]
fill a t@(AppT (AppT ArrowT _) _) e f = do
  let (args, ret) = flattenArrows t
  paramNames <- traverse (const $ newName "x") args
  let e' = foldl appE e (varE <$> paramNames)
  y <- newName "y"
  -- f' = f . \y -> (x1, x2, x3, y)
  let f' = [| $f . $(lamE [varP y] (tupE $ varE <$> (paramNames <> [y]))) |]
  lamE (varP <$> paramNames) (fill a ret e' f')
fill a t@(AppT _ _) e f = do
  let (constr, params) = flattenApps t
  case constr of
    TupleT n -> tupE $ zip [0..n-1] params <&> \(i, t) ->
      fill a t [| $(proji n i) $e |] [| $f . $(eitheri n i) |]
    ListT -> do
      x <- newName "x"
      vf <- newName "f"
      let [param] = params
      let r = fill a param (varE x) [| $(varE vf) . ListLog . Left |]
      [| let
           g [] $(varP vf) = []
           g ($(varP x):xs) $(varP vf) = $r : g xs ($(varE vf) . ListLog . Right)
         in g $e $f
       |]
    ConT typeName -> fillCon (a, typeName, params) e f
    _ -> fail "Not supported"
fill a _ e f = fail "Not supported"

fillCon :: (Name, Name, [Type]) -> Q Exp -> Q Exp -> Q Exp
fillCon (a, typeName, args) e f =
  getFillName (a, typeName, args) >>= \case
    Just name -> [| $(varE name) $e $f |]
    Nothing -> new
  where
    new = do
      fillName <- mkFillName (a, typeName, args)
      fun <- makeFun fillName
      putFillDec (a, typeName, args) fun
      [| $(varE fillName) $e $f |]
    makeFun fillName = do
      info <- reifyDT typeName
      logInfo <- getLogDec (a, typeName, args)
        >>= maybe (pure info) normalizeDec
      ve <- newName "e"
      vf <- newName "f"
      let typeVars = tvName <$> datatypeVars info
      let subst = applySubstitution $ Map.fromList $ zip typeVars args
      body <- caseE (varE ve) $ makeBranch vf <$> zip
        (info & datatypeCons & subst)
        (logInfo & datatypeCons <&> constructorName)
      pure $ FunD fillName [Clause [VarP ve, VarP vf] (NormalB body) []]
    -- C : t -> u -> v -> D
    -- C x y z ->
    -- let r = fill a (t, u, v) (x, y, z) (f . Clog) in
    -- C (proj1 r) (proj2 r) (proj3 r)
    makeBranch vf (con, logConName) = do
      let fields = con & constructorFields
      let conName = con & constructorName
      vars <- sequence (fields $> newName "x")
      let t' = mkTupleT fields
      let e' = case vars of
            [] -> conE '()
            [v] -> varE v
            _ -> tupE $ varE <$> vars
      let re = fill a t' e' [| $(varE vf) . $(conE logConName) |]
      r <- newName "r"
      let body = [| let $(varP r) = $re in
                     $(mkConE conName (length fields) (varE r))
                  |]
      match (conP conName (varP <$> vars)) (normalB body) []

newtype ListLog a = ListLog (Either a (ListLog a)) deriving (Eq, Show, Generic)
instance (Monad m, CoSerial m a) => CoSerial m (ListLog a)
