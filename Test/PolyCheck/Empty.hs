{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.PolyCheck.Empty where

import Data.Void
import Test.QuickCheck hiding (NonEmpty)

data Emptiness a = Empty (a -> Void) | NonEmpty (Gen a)

class IsEmpty a where
  isEmpty :: Emptiness a

instance IsEmpty Void where
  isEmpty = Empty id

instance IsEmpty () where
  isEmpty = NonEmpty arbitraryEmpty

instance IsEmpty Bool where
  isEmpty = NonEmpty arbitraryEmpty

instance IsEmpty Int where
  isEmpty = NonEmpty arbitraryEmpty

instance IsEmpty a => IsEmpty [a] where
  isEmpty = NonEmpty arbitraryEmpty

instance IsEmpty a => IsEmpty (Maybe a) where
  isEmpty = NonEmpty arbitraryEmpty

instance (IsEmpty a, IsEmpty b) => IsEmpty (a, b) where
  isEmpty =
    case isEmpty @a of
      Empty f -> Empty $ \(a, b) -> f a
      NonEmpty a -> case isEmpty @b of
        Empty f -> Empty $ \(a, b) -> f b
        NonEmpty b -> NonEmpty $ (,) <$> a <*> b

class ArbitraryEmpty a where
  arbitraryEmpty :: Gen a

instance ArbitraryEmpty () where
  arbitraryEmpty = arbitrary
instance ArbitraryEmpty Bool where
  arbitraryEmpty = arbitrary
instance ArbitraryEmpty Int where
  arbitraryEmpty = arbitrary

instance (IsEmpty a) => ArbitraryEmpty [a] where
  arbitraryEmpty =
    case isEmpty @a of
      Empty _ -> pure []
      NonEmpty g -> liftArbitrary g

instance (IsEmpty a) => ArbitraryEmpty (Maybe a) where
  arbitraryEmpty =
    case isEmpty @a of
      Empty _ -> pure Nothing
      NonEmpty g -> liftArbitrary g

instance (ArbitraryEmpty a, ArbitraryEmpty b) => ArbitraryEmpty (a, b) where
  arbitraryEmpty = liftArbitrary2 arbitraryEmpty arbitraryEmpty

gen0 :: Gen [(Int, Maybe Void)]
gen0 = arbitraryEmpty
