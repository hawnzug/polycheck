{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
module Test.PolyCheck.TH.Empty where

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
import GHC.Generics (Generic)
import Test.QuickCheck hiding (monomorphic)
import Data.Traversable (for)

makeEmpty :: Type -> Q [Dec]
makeEmpty (VarT a) = undefined
makeEmpty (ConT b) = pure []
makeEmpty (TupleT 0) = pure []
makeEmpty (AppT (AppT ArrowT arg) ret) = do
  empArg <- isEmpty arg
  empRet <- isEmpty ret
  undefined
makeEmpty t@(AppT _ _) = do
  let (constr, params) = flattenApps t
  case constr of
    TupleT _ ->
      -- All fields are nonempty
      concat <$> traverse makeEmpty params
    ListT -> let [param] = params in do
      emp <- isEmpty param
      if emp
      then [d| instance {-# Overlapping #-} Arbitrary $(pure t) where
                 arbitrary = pure []
             |]
      else makeEmpty param
    ConT typeName -> undefined
    _ -> fail "Not supported"
makeEmpty _ = fail "Not supported"
