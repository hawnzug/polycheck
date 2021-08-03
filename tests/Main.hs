{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -ddump-splices #-}

module Main where

import qualified StrictlyPositive
import GHC.Generics (Generic)
import Text.Show.Functions
import Test.PolyCheck.TH (monomorphic)
import Test.QuickCheck hiding (monomorphic)

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
  deriving (Eq, Show)

myreverse :: MyList a -> MyList a
myreverse l = go l MyNil where
  go MyNil r = r
  go (MyCons h t) r = go t (MyCons h r)

instance Arbitrary a => Arbitrary (MyList a) where
  arbitrary = foldr MyCons MyNil <$> listOf arbitrary

prop2 :: Eq a => MyList a -> Bool
prop2 l = l == (myreverse (myreverse l))

prop3 :: (Eq a, Eq b) => [(a, b)] -> Bool
prop3 l = l == reverse (reverse l)

data Bar a = Bar1 (a -> a) | Bar2 (a -> a)
  deriving (Show, Generic)
instance (CoArbitrary a, Arbitrary a) => Arbitrary (Bar a) where
  arbitrary = oneof [Bar1 <$> arbitrary, Bar2 <$> arbitrary]
instance (CoArbitrary a, Arbitrary a) => CoArbitrary (Bar a)

data Foo a b c = Foo (Bar a) (Bar (Maybe a)) (c -> c)
  deriving (Show)
instance (CoArbitrary a, Arbitrary a, CoArbitrary b, Arbitrary b, CoArbitrary c, Arbitrary c)
  => Arbitrary (Foo a b c) where
  arbitrary = Foo <$> arbitrary <*> arbitrary <*> arbitrary

prop4 :: Foo a (Bar (a, a)) (Maybe a) -> Bool
prop4 _ = True

data T1 a b = T1 (a -> a) (b -> b) deriving Show
instance (CoArbitrary a, Arbitrary a, CoArbitrary b, Arbitrary b) => Arbitrary (T1 a b) where
  arbitrary = T1 <$> arbitrary <*> arbitrary
prop5 :: (T1 a b, T1 a Int) -> Bool
prop5 _ = True

prop6 :: Bar a -> Bool
prop6 _ = True

prop7 :: Bar a -> Bool
prop7 _ = True

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
$(monomorphic 'prop4)
$(monomorphic 'prop5)
$(monomorphic 'prop6)
$(monomorphic 'prop7)
$(monomorphic 'prop8)

main :: IO ()
main = do
  quickCheck prop0_mono
  quickCheck prop1_mono
  quickCheck prop2_mono
  quickCheck prop3_mono
  quickCheck prop4_mono
  quickCheck prop5_mono
  quickCheck prop6_mono
  quickCheck prop7_mono
  quickCheck prop8_mono
  pure ()
