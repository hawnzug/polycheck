{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -ddump-splices #-}

module Main where

import qualified StrictlyPositive
import GHC.Generics (Generic)
import Test.PolyCheck.TH (monomorphic)
import Test.SmallCheck
import Test.SmallCheck.Series

$(StrictlyPositive.main)

prop0 :: (a -> b) -> [a] -> Bool
prop0 f xs = length (fmap f xs) == 0

mymap :: a -> Maybe a -> Maybe (a, a) -> a
mymap x Nothing _ = x
mymap _ (Just x) _ = x

mymap' :: a -> Maybe a -> Maybe (a, a) -> a
mymap' x Nothing _ = x
mymap' y (Just x) _ = y

prop1 :: Eq a => a -> Maybe a -> Maybe (a, a) -> Bool
prop1 x y z = mymap x y z == mymap' x y z

data MyList a = MyNil | MyCons a (MyList a)
  deriving (Eq, Show, Generic)
instance (Monad m, Serial m a) => Serial m (MyList a)

myreverse :: MyList a -> MyList a
myreverse l = go l MyNil where
  go MyNil r = r
  go (MyCons h t) r = go t (MyCons h r)

prop2 :: Eq a => MyList a -> Bool
prop2 l = l == (myreverse (myreverse l))

prop3 :: (Eq a, Eq b) => [(a, b)] -> Bool
prop3 l = l == reverse (reverse l)

type MyPair a b = (a, b)
type MyMaybe a = MyPair a MyInt
type MyInt = Int
type MyBool = Bool

prop8 :: MyMaybe a -> MyBool
prop8 _ = True

$(monomorphic 'prop0)
$(monomorphic 'prop1)
$(monomorphic 'prop2)
$(monomorphic 'prop3)
$(monomorphic 'prop8)

main :: IO ()
main = do
  smallCheck 5 prop0_mono
  smallCheck 5 prop1_mono
  smallCheck 5 prop2_mono
  smallCheck 5 prop3_mono
  smallCheck 5 prop8_mono
  pure ()
