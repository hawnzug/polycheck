{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import GHC.Generics (Generic)
import Test.PolyCheck.TH (monomorphic)
import Test.SmallCheck
import Test.SmallCheck.Drivers
import Control.Monad
import Data.IORef

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

smallCheck' :: Testable IO a => Depth -> a -> IO Integer
smallCheck' d prop = do
  numCases <- newIORef 0
  smallCheckWithHook d (\_ -> modifyIORef' numCases (+1)) prop
  readIORef numCases

main :: IO ()
main = do
  run (prop_nat @Int) prop_nat_mono
  run (prop_map @Int @Int) prop_map_mono
  run (prop_takeWhile @Int) prop_takeWhile_mono
  -- run (prop_zipWith @Int @Int @Int) prop_zipWith_mono
  where
    run p p' = do
      m <- smallCheck' 5 p
      n <- smallCheck' 5 p'
      print (m, n)
