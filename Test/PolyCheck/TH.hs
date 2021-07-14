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
monomorphic func = do
  -- reifyType for template-haskell >= 2.11 <= 2.15
  let reifyType name = reify name <&> \(VarI _ t _) -> t
  ty <- reifyType func >>= resolveTypeSynonyms
  (vars, funcType, params, returnType) <- destructPolyFn ty
  qStateInit (last vars) (nameBase func)
  let t = case params of
        [x] -> x
        _ -> foldl AppT (TupleT $ length params) params
  let (logTypeNames, logConNames, fillNames) = unzip3 $ vars <&> \var ->
        let make s = mkName $ s <> nameBase func <> nameBase var in
        (make "TestLog", make "TestLogCon", make "testfill")
  mapM_ (genLogs t) $ zip3 vars logTypeNames logConNames
  substLogDecs vars logTypeNames
  res <- genRes (ConT <$> logTypeNames) vars t
  mapM_ (genFill t) $ zip3 vars fillNames logConNames
  let monoName = mkName $ nameBase func <> "_mono"
  let monoTypeName = mkName $ "Mono" <> nameBase func
  let monoTypeConName = mkName $ "MonoC" <> nameBase func
  let subst = applySubstitution $ Map.fromList $ zip vars (ConT <$> logTypeNames)
  genMonoType (length params) monoTypeName monoTypeConName fillNames res (subst t)
  genMonoFun (length params) func monoName monoTypeName monoTypeConName (subst returnType)
  genEmptyFun func vars funcType
  concat <$> sequence [getLogDecls, getResDecls, getFillDecls, getDecls]

genEmptyFun :: Name -> [Name] -> Type -> Q ()
genEmptyFun func vars ty = do
  let emptyName = mkName $ (nameBase func) <> "_empty"
  let tyEmpty = applySubstitution (Map.fromList $ vars <&> (, ConT ''Void)) ty
  let sig = SigD emptyName tyEmpty
  let decl = ValD (VarP emptyName) (NormalB (VarE func)) []
  putDecls [sig, decl]

-- | Calculate the log type of @t@ w.r.t. @a@
logt :: Name -> Type -> Q Type
logt a (VarT b) | a == b = [t| () |]
logt a (VarT b) = [t| Void |]
logt a (ConT b) = [t| Void |]
logt a (TupleT 0) = [t| Void |]
logt a t@(AppT (AppT ArrowT _) _) = do
  let (args, ret) = flattenArrows t
  logret <- logt a ret
  pure $ appTuple (args ++ [logret])
logt a t@(AppT _ _) = do
  let (constr, params) = flattenApps t
  case constr of
    TupleT n -> appEithers <$> traverse (logt a) params
    ListT -> let [param] = params in [t| ListLog $(logt a param) |]
    ConT conName -> logCon a (conName, params)
    _ -> fail "Not supported"
logt _ _ = fail "Not supported"

logCon :: Name -> (Name, [Type]) -> Q Type
logCon a (datatypeName, args) =
  getLogDec (a, datatypeName, args)
  >>= maybe new (\(DataD _ name _ _ _ _) -> conT name)
  where
  new = do
    info <- reifyDT datatypeName
    logTypeName <- newUniqueName $ nameBase datatypeName <> "Log"
    putLogDec (a, datatypeName, args) $ DataD [] logTypeName [] Nothing [] []
    logCons <-
      let typeVars = tvName <$> datatypeVars info in
      let subst = applySubstitution $ Map.fromList $ zip typeVars args in
      forM (datatypeCons info) $ \con -> do
        logFields <- traverse (logt a . subst) (constructorFields con)
        name <- newUniqueName $ nameBase (constructorName con) <> "LogC"
        pure $ makeCon name [appEithers logFields]
    putDecls =<< [d| instance CoArbitrary $(conT logTypeName) |]
    putLogDec (a, datatypeName, args) $
      DataD [] logTypeName [] Nothing logCons
      [DerivClause Nothing (ConT <$> [''Eq, ''Show, ''Generic])]
    conT logTypeName

resCon :: [Name] -> (Type -> Type) -> (Type -> Type) -> (Name, [Type]) -> Q Type
resCon as substLog substArg (datatypeName, args) = do
  info <- reifyDT datatypeName
  resTypeName <- newUniqueName $ nameBase datatypeName <> "Res"
  putResType (datatypeName, substArg <$> args) $ DataD [] resTypeName [] Nothing [] []
  let typeVars = info & datatypeVars <&> tvName
  constr <- residualConstructor info typeVars
  let decl = DataD [] resTypeName (plainTV <$> typeVars) Nothing constr
        [DerivClause Nothing (ConT <$> [''Show, ''Generic])]
  putResType (datatypeName, substArg <$> args) decl
  resInfo <- normalizeDec decl
  let ctx = traverse (\a -> [t| Arbitrary $(varT a) |]) typeVars
  let typ = appT (conT ''Arbitrary) $
            foldl appT (conT resTypeName) (varT <$> typeVars)
  let monoType = foldl appT (conT datatypeName) (typeVars $> [t| () |])
  let f = toRes info resInfo
  let dec = funD 'arbitrary
        [clause [] (normalB [| (arbitrary :: Gen $monoType) >>= $f |]) []]
  putDecls . pure =<< instanceD ctx typ [dec]
  conT resTypeName
  where
    residualConstructor info typeVars = do
      let substLog' = applySubstitution $ Map.fromList $ zip typeVars (substLog <$> args)
      let substArg' = applySubstitution $ Map.fromList $ zip typeVars (substArg <$> args)
      forM (info & datatypeCons) $ \con -> do
        fields <- traverse (residual typeVars substLog' substArg') (con & constructorFields)
        name <- newUniqueName $ (con & constructorName & nameBase) <> "ResC"
        pure $ makeCon name fields
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
      TupleT n -> appTuple <$> traverse (residual as substLog substArg) params
      ListT -> let [param] = params in [t| [$(residual as substLog substArg param)] |]
      ConT conName -> getResType (conName, params) >>= \case
        Just (DataD _ name _ _ _ _) -> pure $ foldl AppT (ConT name) params
        Nothing -> do
          con <- resTypeRequired as (conName, params) >>= \case
            True -> resCon as substLog substArg (conName, params)
            False -> pure constr
          foldl AppT con <$> traverse (residual as substLog substArg) params
      _ -> fail "Not supported"
  _ -> fail "Not supported"

fillCon :: Name -> (Name, [Type]) -> Q Exp -> Q Exp -> Q Exp
fillCon a (datatypeName, args) e f = do
  fillName <- newUniqueName $ "fill_" <> nameBase datatypeName
  putFillDecl (a, datatypeName, args) $ FunD fillName []
  fun <- makeFun fillName
  putFillDecl (a, datatypeName, args) fun
  [| $(varE fillName) $e $f |]
  where
    makeFun fillName = do
      info <- reifyDT datatypeName
      logInfo <- getLogDec (a, datatypeName, args)
        >>= maybe (pure info) normalizeDec
      resInfo <- getResType (datatypeName, args)
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
      let t' = appTuple fields
      let e' = case vars of
            [] -> conE '()
            [v] -> varE v
            _ -> tupE $ varE <$> vars
      let re = fill a t' e' [| $(varE vf) . $(conE logConName) |]
      r <- newName "r"
      let body = [| let $(varP r) = $re in
                     $(appCon conName (length fields) (varE r))
                  |]
      match (conP resConName (varP <$> vars)) (normalB body) []

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

genLogs :: Type -> (Name, Name, Name) -> Q ()
genLogs t (a, datatypeName, conName) = do
  log <- logt a t
  putLogDec (a, a, []) $
    DataD [] datatypeName [] Nothing [makeCon conName [log]]
    [DerivClause Nothing [ConT ''Eq, ConT ''Show, ConT ''Generic]]
  putDecls =<< [d| instance CoArbitrary $(conT datatypeName) |]

genRes :: [Type] -> [Name] -> Type -> Q Type
genRes logs as t = do
  let subst = applySubstitution . Map.fromList . zip as
  residual as (subst logs) id t <&> subst (repeat $ TupleT 0)

genFill :: Type -> (Name, Name, Name) -> Q ()
genFill t (a, fillName, logConName) = do
  x <- newName "e"
  fillDecl <- funD fillName $ pure $
        clause [varP x] (normalB (fill a t (varE x) (conE logConName))) []
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
      (makeCon monoTypeConName [t]) []
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

instance CoArbitrary Void where
  coarbitrary = absurd

data ListLog a = ListLogA a | ListLogB (ListLog a) deriving (Eq, Show, Generic)
instance (CoArbitrary a) => CoArbitrary (ListLog a)
