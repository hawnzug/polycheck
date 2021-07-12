{-# LANGUAGE TemplateHaskell #-}
module Test.PolyCheck.TH.State where

import Control.Arrow
import Data.Functor
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Datatype
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

instance TypeSubstitution Dec where
  applySubstitution m = \case
    DataD ctx name [] kind cons derivs ->
      DataD ctx name [] kind (f <$> cons) derivs
    _ -> error "TypeSubstitution: only works for data declarations with no type variable"
    where
      f (NormalC name bts) = NormalC name $
        fmap (second $ applySubstitution m) bts
      f _ = error "TypeSubstitution: not a normal constructor"

  freeVariables = \case
    DataD _ _ [] _ cons _ -> cons >>= f
    _ -> error "TypeSubstitution: only works for data declarations with no type variable"
    where
      f (NormalC _ bts) = bts >>= freeVariables . snd
      f _ = error "TypeSubstitution: not a normal constructor"

type Key = (Name, Name, [Type])

data State = State
  { freshName :: Int
  , funcName :: String
  , lastTV :: Name
  , decls :: [Dec]
  , infom :: Map Name DatatypeInfo
  , logm :: Map Key Dec
  , resm :: Map (Name, [Type]) Dec
  , fillm :: Map Key Dec
  , tvOccur :: Map Name [Bool]
  , tvSP :: Map Name [Bool]
  }

qStateInit :: Name -> String -> Q ()
qStateInit a func = qPutQ $ State
  { freshName = 0
  , funcName = func
  , lastTV = a
  , decls = []
  , infom = Map.empty
  , logm = Map.empty
  , resm = Map.empty
  , fillm = Map.empty
  , tvOccur = Map.empty
  , tvSP = Map.empty
  }

isLastTV :: Name -> Q Bool
isLastTV a = do
  Just s@State{lastTV} <- qGetQ
  pure $ a == lastTV

newUniqueName :: String -> Q Name
newUniqueName name = do
  Just s@State{freshName, funcName} <- qGetQ
  qPutQ $ s{freshName = freshName + 1}
  pure $ mkName $ name <> show freshName <> funcName

getDecls :: Q [Dec]
getDecls = do
  Just s@State{decls} <- qGetQ
  pure decls

putDecls :: [Dec] -> Q ()
putDecls d = do
  Just s@State{decls} <- qGetQ
  qPutQ $ s{decls = decls <> d}

getDatatypeInfo :: Name -> Q (Maybe DatatypeInfo)
getDatatypeInfo name =
  qGetQ <&> (>>= (Map.lookup name . infom))

getLogDecls :: Q [Dec]
getLogDecls = do
  Just s@State{logm} <- qGetQ
  pure $ Map.elems logm

getLogDec :: Key -> Q (Maybe Dec)
getLogDec k = do
  Just s@State{logm} <- qGetQ
  pure $ Map.lookup k logm

putLogDec :: Key -> Dec -> Q ()
putLogDec k dec@(DataD _ name _ _ _ _) = do
  Just s@State{logm} <- qGetQ
  qPutQ $ s{logm = Map.insert k dec logm}

substLogDecs :: [Name] -> [Name] -> Q ()
substLogDecs vars datatypeNames = do
  Just s@State{logm} <- qGetQ
  let m = ConT <$> Map.fromList (zip vars datatypeNames)
  let logm' = applySubstitution m <$> logm
  let f dec@(DataD _ name _ _ _ _) = normalizeDec dec <&> (name,)
  infom' <- Map.fromList <$> traverse f (Map.elems logm')
  qPutQ $ s{infom = infom', logm = logm'}

getResDecls :: Q [Dec]
getResDecls = do
  Just s@State{resm} <- qGetQ
  pure $ Map.elems resm

getResType :: (Name, [Type]) -> Q (Maybe Dec)
getResType k = do
  Just s@State{resm} <- qGetQ
  pure $ Map.lookup k resm

putResType :: (Name, [Type]) -> Dec -> Q ()
putResType k v = do
  Just s@State{resm} <- qGetQ
  qPutQ $ s{resm = Map.insert k v resm}

getFillDecls :: Q [Dec]
getFillDecls = do
  Just s@State{fillm} <- qGetQ
  pure $ Map.elems fillm

getFillDecl :: Key -> Q (Maybe Dec)
getFillDecl k = do
  Just s@State{fillm} <- qGetQ
  pure $ Map.lookup k fillm

putFillDecl :: Key -> Dec -> Q ()
putFillDecl k v = do
  Just s@State{fillm} <- qGetQ
  qPutQ $ s{fillm = Map.insert k v fillm}

getTvOccur :: Name -> Q (Maybe [Bool])
getTvOccur k = do
  Just s@State{tvOccur} <- qGetQ
  pure $ Map.lookup k tvOccur

putTvOccur :: Name -> [Bool] -> Q ()
putTvOccur k v = do
  Just s@State{tvOccur} <- qGetQ
  qPutQ $ s{tvOccur = Map.insert k v tvOccur}

getTvSP :: Name -> Q (Maybe [Bool])
getTvSP k = do
  Just s@State{tvSP} <- qGetQ
  pure $ Map.lookup k tvSP

putTvSP :: Name -> [Bool] -> Q ()
putTvSP k v = do
  Just s@State{tvSP} <- qGetQ
  qPutQ $ s{tvSP = Map.insert k v tvSP}
