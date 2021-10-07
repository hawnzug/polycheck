{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}

module Main where

import GHC.Generics (Generic)
import Text.Show.Functions
import Test.PolyCheck.TH (monomorphic)
import Test.QuickCheck hiding (monomorphic)
import qualified Test.QuickCheck as QC
import Control.Monad
import Text.Printf (printf)

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

numTestsFail :: Testable prop => prop -> IO [Int]
numTestsFail prop = do
  replicateM 10000 $
    numTests <$>
    quickCheckWithResult stdArgs{chatty=False} prop

main :: IO ()
main = do
  (stats, qc, pc) <- unzip3 <$> sequence
    [ run $(QC.monomorphic 'prop_nat) prop_nat_mono
    , run $(QC.monomorphic 'prop_map) prop_map_mono
    , run $(QC.monomorphic 'prop_takeWhile) prop_takeWhile_mono
    , run $(QC.monomorphic 'prop_zipWith) prop_zipWith_mono
    ]
  writeFile "../results/quickcheck.txt" $ unlines stats
  writeFile "../results/quickcheck-nums.txt" $ unlines (qc <> pc)
  where
    run p p' = do
      m <- numTestsFail p
      n <- numTestsFail p'
      let (avg0, dev0) = calc m
      let (avg1, dev1) = calc n
      pure (printf "%.2f(%.2f) %.2f(%.2f)" avg0 dev0 avg1 dev1,
            unwords $ show <$> m,
            unwords $ show <$> n)
    calc xs = (avg, dev :: Float)
      where
        nums = fromIntegral <$> xs
        n = fromIntegral $ length nums
        avg = sum nums / n
        dev = sqrt $ sum (map (\x -> (x - avg) ^ 2) nums) / n

