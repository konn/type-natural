{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Shared where

import Data.Kind (Type)
import Data.Type.Natural
import Data.Type.Ordinal
import GHC.TypeNats
import Numeric.Natural
import Test.QuickCheck
import Test.QuickCheck.Instances ()

instance (KnownNat n, 0 < n) => Arbitrary (Ordinal n) where
  arbitrary = elements $ enumOrdinal sNat
  shrink 0 = []
  shrink n = [0 .. pred n]

instance Arbitrary SomeNat where
  arbitrary = sized $ \n -> someNatVal <$> resize n arbitrary
  shrink (SomeNat pn) =
    someNatVal <$> shrink (natVal pn)

instance Arbitrary SomeSNat where
  arbitrary = sized $ \n -> toSomeSNat <$> resize n arbitrary
  shrink (SomeSNat pn) =
    toSomeSNat <$> shrink (natVal pn)

type family Sing = (r :: k -> Type)

class Demote k where
  type Demoted k
  type Demoted k = k
  demote :: Sing (a :: k) -> Demoted k

class Known a where
  sing :: Sing a

instance KnownNat n => Known n where
  sing = sNat

instance Known 'True where
  sing = STrue

instance Known 'False where
  sing = SFalse

instance Known 'LT where
  sing = SLT

instance Known 'GT where
  sing = SGT

instance Known 'EQ where
  sing = SEQ

type instance Sing = SNat

instance Demote Nat where
  type Demoted Nat = Natural
  demote = toNatural

type instance Sing = SOrdering

instance Demote Ordering where
  demote SLT = LT
  demote SEQ = EQ
  demote SGT = GT

type instance Sing = SBool

instance Demote Bool where
  demote STrue = True
  demote SFalse = False
