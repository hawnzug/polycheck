{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import GHC.Generics (Generic)
import Test.PolyCheck.TH (monomorphic)
import Test.SmallCheck
import Test.SmallCheck.Drivers
import Control.Monad

applyn :: Int -> a -> (a -> a) -> a
applyn 0 x f = x
applyn n x f = f (applyn (n-1) x f)

prop_nat :: Eq a => a -> (a -> a) -> Bool
prop_nat x f = applyn 2 x f == applyn 3 x f

$(monomorphic 'prop_nat)

swap2 :: [a] -> [a]
swap2 (x:y:xs) = y:x:xs
swap2 xs = xs

swap2' :: [a] -> [a]
swap2' = reverse . swap2 . reverse

prop_map :: Eq b => (a -> b) -> [a] -> Bool
prop_map f xs = map f (swap2 xs) == map f xs

prop_takeWhile :: Eq a => (a -> Bool) -> [a] -> Bool
prop_takeWhile f xs = takeWhile f (swap2' xs) == takeWhile f xs

prop_zipWith :: Eq c => (a -> b -> c) -> [a] -> [b] -> Bool
prop_zipWith f xs ys = zipWith f (swap2' xs) ys == zipWith f xs ys

$(monomorphic 'prop_map)
$(monomorphic 'prop_takeWhile)
$(monomorphic 'prop_zipWith)

main :: IO ()
main = do
  smallCheck 5 (prop_nat @Int)
  smallCheck 5 prop_nat_mono
  smallCheck 5 (prop_map @Int @Int)
  smallCheck 5 prop_map_mono
  smallCheck 5 (prop_takeWhile @Int)
  smallCheck 5 prop_takeWhile_mono
  -- smallCheck 2 (prop_zipWith @Int @Int @Int)
  smallCheck 5 prop_zipWith_mono
