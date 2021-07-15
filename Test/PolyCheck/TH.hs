{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
module Test.PolyCheck.TH where

import Test.PolyCheck.TH.State
import Test.PolyCheck.TH.TypeExp
import Test.PolyCheck.TH.Predicate

import Data.List (intersperse)
import Data.Functor
import Data.Function
import Control.Monad
import Language.Haskell.TH
import Language.Haskell.TH.Datatype
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Void (Void, absurd)
import GHC.Generics (Generic)
import Test.QuickCheck hiding (monomorphic)
import Data.Traversable (for)

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
  let (logTypeNames, logConNames, fillNames) = unzip3 $ vars <&> \var ->
        let make s = mkName $ s <> nameStr <> nameBase var in
        (make "TestLog", make "TestLogCon", make "testfill")
  genLogs t vars logTypeNames logConNames
  substLogDecs vars logTypeNames
  res <- genRes (ConT <$> logTypeNames) vars t
  genFill t vars fillNames logConNames
  let subst = applySubstitution $ Map.fromList $ zip vars (ConT <$> logTypeNames)
  genMonoType (length params) monoTypeName monoTypeConName fillNames res (subst t)
  genMonoFun (length params) name monoName monoTypeName monoTypeConName (subst returnType)
  concat <$> sequence [getLogDecls, getResDecls, getFillDecls, getDecls]
  where
    -- reifyType for template-haskell >= 2.11 <= 2.15
    reifyType name = reify name <&> \(VarI _ t _) -> t
    nameStr = nameBase name
    monoName = mkName $ nameStr <> "_mono"
    monoTypeName = mkName $ "Mono" <> nameStr
    monoTypeConName = mkName $ "MonoC" <> nameStr

genLogs :: Type -> [Name] -> [Name] -> [Name] -> Q ()
genLogs t vars typeNames conNames =
  mapM_ go $ zip3 vars typeNames conNames
  where
    go (a, typeName, conName) = do
      log <- logt a t
      putLogDec (a, a, []) $
          DataD [] typeName [] Nothing [mkConD conName [log]]
          [DerivClause Nothing [ConT ''Eq, ConT ''Show, ConT ''Generic]]
      putDecls =<< [d| instance CoArbitrary $(conT typeName) |]

genRes :: [Type] -> [Name] -> Type -> Q Type
genRes logs vars t = do
  let subst = applySubstitution . Map.fromList . zip vars
  residual vars (subst logs) id t <&> subst (repeat $ TupleT 0)

genFill :: Type -> [Name] -> [Name] -> [Name] -> Q ()
genFill t vars fillNames conNames =
  mapM_ go $ zip3 vars fillNames conNames
  where
    go (a, fillName, conName) = do
      x <- newName "e"
      fillDecl <-
        funD fillName $
        [clause [varP x] (normalB $ fill a t (varE x) (conE conName)) []]
      putFillDecl (a, fillName, []) fillDecl

genMonoType :: Int -> Name -> Name -> [Name] -> Type -> Type -> Q ()
genMonoType numArgs monoTypeName monoTypeConName fillNames resType t = do
  x <- newName "x"
  instDecl <-
    [d|
     instance Arbitrary $(conT monoTypeName) where
       arbitrary = $fills <$> (arbitrary :: Gen $(pure resType))
     instance Show $(conT monoTypeName) where
       show $(conP monoTypeConName [varP x]) = $(showMono x)
     |]
  putDecls $ monoTypeDecl : instDecl
  where
    monoTypeDecl = NewtypeD [] monoTypeName [] Nothing
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
  monoDecl <- funD monoName
    [clause [conP monoTypeConName [varP x]] (normalB body) []]
  putDecls [monoSig, monoDecl]

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
      putDecls =<< [d| instance CoArbitrary $(conT logTypeName) |]
      conT logTypeName

-- | Replace all the type variables that are not strictly positive by
-- their corresponding log types.
residual :: [Name] -- ^ All the type variables a, b, c, ...
         -> (Type -> Type) -- ^ See 'resCon'
         -> (Type -> Type) -- ^ See 'resCon'
         -> Type -- ^ The type t
         -> Q Type
residual as substLog substArg = \case
  t@(VarT _) -> pure t
  t@(ConT _) -> pure t
  t@(TupleT 0) -> pure t
  t@(AppT (AppT ArrowT arg) ret) ->
    [t| $(pure $ substLog arg) ->
        $(residual as substLog substArg ret) |]
  t@(AppT _ _) -> do
    let (constr, params) = flattenApps t
    case constr of
      TupleT _ -> mkTupleT <$> traverse (residual as substLog substArg) params
      ListT -> let [param] = params in [t| [$(residual as substLog substArg param)] |]
      ConT typeName -> resCon as substLog substArg (typeName, params)
      _ -> fail "Not supported"
  _ -> fail "Not supported"

resCon :: [Name] -> (Type -> Type) -> (Type -> Type) -> (Name, [Type]) -> Q Type
resCon as substLog substArg (typeName, args) =
  getResTypeName (typeName, args) >>= \case
    Just name -> pure $ foldl AppT (ConT name) args
    Nothing -> do
      resType <- resTypeRequired as (typeName, args) >>= \case
        True -> new
        False -> conT typeName
      resArgs <- traverse (residual as substLog substArg) args
      pure $ foldl AppT resType resArgs
  where
    new = do
      info <- reifyDT typeName
      let argsSubsted = substArg <$> args
      resTypeName <- mkResTypeName (typeName, argsSubsted)
      let typeVars = info & datatypeVars <&> tvName
      constr <- residualConstructor info typeVars
      let decl = DataD [] resTypeName (plainTV <$> typeVars) Nothing constr
              [DerivClause Nothing (ConT <$> [''Show, ''Generic])]
      putResDec (typeName, argsSubsted) decl
      resInfo <- normalizeDec decl
      let ctx = traverse (\a -> [t| Arbitrary $(varT a) |]) typeVars
      let typ = appT (conT ''Arbitrary) $
                  foldl appT (conT resTypeName) (varT <$> typeVars)
      let monoType = foldl appT (conT typeName) (typeVars $> [t| () |])
      let f = toRes info resInfo
      let dec = funD 'arbitrary
              [clause [] (normalB [| (arbitrary :: Gen $monoType) >>= $f |]) []]
      putDecls . pure =<< instanceD ctx typ [dec]
      conT resTypeName
    residualConstructor info typeVars = do
      let substLog' = applySubstitution $ Map.fromList $ zip typeVars (substLog <$> args)
      let substArg' = applySubstitution $ Map.fromList $ zip typeVars (substArg <$> args)
      forM (info & datatypeCons) $ \con -> do
        fields <- traverse (residual typeVars substLog' substArg') (con & constructorFields)
        name <- newUniqueName $ (con & constructorName & nameBase) <> "ResC"
        pure $ mkConD name fields
    toRes info resInfo = do
      x <- newName "x"
      lamE [varP x] $ caseE (varE x) $ makeBranch <$> zip
        (info & datatypeCons) (resInfo & datatypeCons <&> constructorName)
    -- C x y z -> pure Cres <*> arbitrary <*> arbitrary <*> arbitrary
    makeBranch (con, resConName) = do
      let fields = con & constructorFields
      let conName = con & constructorName
      let body = foldl
            (\x y -> [| $x <*> $y |])
            [| pure $(conE resConName) |]
            (fields $> [| arbitrary |])
      match (conP conName (fields $> wildP)) (normalB body) []

fill :: Name -- ^ The type variable a
     -> Type -- ^ The type t
     -> Q Exp -- ^ The skeleton e
     -> Q Exp -- ^ The label prefix f
     -> Q Exp
fill a (VarT b) e f | a == b = [| $f $e |]
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
      let r = fill a param (varE x) [| $(varE vf) . ListLogA |]
      [| let
           g [] $(varP vf) = []
           g ($(varP x):xs) $(varP vf) = $r : g xs ($(varE vf) . ListLogB)
         in g $e $f
       |]
    ConT conName -> getFillDecl (a, conName, params) >>= \case
      Just (FunD name _) -> [| $(varE name) $e $f |]
      Nothing -> fillCon a (conName, params) e f
    _ -> fail "Not supported"
fill a _ e f = fail "Not supported"

fillCon :: Name -> (Name, [Type]) -> Q Exp -> Q Exp -> Q Exp
fillCon a (typeName, args) e f = do
  fillName <- newUniqueName $ "fill_" <> nameBase typeName
  putFillDecl (a, typeName, args) $ FunD fillName []
  fun <- makeFun fillName
  putFillDecl (a, typeName, args) fun
  [| $(varE fillName) $e $f |]
  where
    makeFun fillName = do
      info <- reifyDT typeName
      logInfo <- getLogDec (a, typeName, args)
        >>= maybe (pure info) normalizeDec
      resInfo <- getResDec (typeName, args)
        >>= maybe (pure info) normalizeDec
      isLast <- isLastTV a
      ve <- newName "e"
      vf <- newName "f"
      let typeVars = tvName <$> datatypeVars info
      let subst = applySubstitution $ Map.fromList $ zip typeVars args
      body <- caseE (varE ve) $ makeBranch vf <$> zip3
        ((if isLast then info else resInfo) & datatypeCons & subst)
        (logInfo & datatypeCons <&> constructorName)
        (resInfo & datatypeCons <&> constructorName)
      pure $ FunD fillName [Clause [VarP ve, VarP vf] (NormalB body) []]
    -- C : t -> u -> v -> D
    -- Cres x y z ->
    -- let r = fill a (t, u, v) (x, y, z) (f . Clog) in
    -- C (proj1 r) (proj2 r) (proj3 r)
    makeBranch vf (con, logConName, resConName) = do
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
      match (conP resConName (varP <$> vars)) (normalB body) []

instance CoArbitrary Void where
  coarbitrary = absurd

data ListLog a = ListLogA a | ListLogB (ListLog a) deriving (Eq, Show, Generic)
instance (CoArbitrary a) => CoArbitrary (ListLog a)
