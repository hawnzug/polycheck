{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
module StrictlyPositive where

import Test.PolyCheck.TH.State
import Test.PolyCheck.TH.Predicate

import Data.Void (Void)
import Control.Monad
import Data.Functor.Const
import Language.Haskell.TH

data T0 a = T0 (a -> Bool)
data T1 a = T1 a (T0 a)
data T2 a = T21 a | T22 (T2 a)
data T3 a = T31 | T32 (T3 a -> Bool)
data T4 a = T4 (Either (Maybe a) (T4 a))

main :: Q [Dec]
main = do
  na <- newName "a"
  qStateInit na "prop"
  let test = tvStrictlyPositive na
  let occ qt = do
        t <- qt
        tvOccurs na t >>= \case
          True -> pure ()
          False -> fail $ pprint t <> ": no occurrence"
  let pos qt = do
        t <- qt
        test t >>= \case
          True -> pure ()
          False -> fail $ pprint t <> ": not strictly positive"
  let neg qt = do
        t <- qt
        test t >>= \case
          True -> fail $ pprint t <> ": strictly positive"
          False -> pure ()
  let empty qt = do
        t <- qt
        isEmpty t >>= \case
          True -> pure ()
          False -> fail $ pprint t <> ": nonempty"
  let a = varT na

  occ [t| T2 $a |]
  occ [t| T4 $a |]

  pos [t| T2 $a |]
  pos [t| T3 $a |]
  pos [t| T4 $a |]

  pos [t| $a |]
  pos [t| Int |]
  pos [t| Int -> $a |]
  pos [t| ($a, $a) |]
  pos [t| ($a, Int) |]
  pos [t| Maybe $a |]
  pos [t| Maybe ($a, $a) |]
  pos [t| Const $a (T0 $a) |]
  pos [t| Either $a $a |]
  pos [t| Const Int (T0 $a) -> $a |]

  neg [t| $a -> $a |]
  neg [t| T0 $a |]
  neg [t| T1 $a |]
  neg [t| Maybe (T0 $a) |]
  neg [t| Const (T0 $a) $a |]
  neg [t| Either $a (Maybe (T1 (Maybe $a))) |]

  empty [t| Void |]
  empty [t| () -> Void |]
  empty [t| Int -> Void |]
  empty [t| (Bool, Void) |]
  empty [t| ((Int, Int), Void) |]
  empty [t| (Void, [Void]) |]
  empty [t| Either Void Void |]
  empty [t| T1 Void |]

  pure []
