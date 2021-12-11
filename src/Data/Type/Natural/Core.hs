{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoStarIsType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Data.Type.Natural.Core
  ( SNat (.., Zero, Succ),
    ZeroOrSucc (..),
    viewNat,
    sNat,
    withKnownNat,
    (%+),
    (%-),
    (%*),
    (%^),
    sDiv,
    sMod,
    sLog2,
    (%<=?),
    sCmpNat,
    sCompare,
    Succ,
    S,
    sSucc,
    sS,
    Pred,
    sPred,
    Zero,
    One,
    sZero,
    sOne,
    Equality (..),
    equalAbsurdFromBool,
    type (===),
    (%~),
    sFlipOrdering,
    FlipOrdering,
    SOrdering (..),
    SBool (..),
    -- Re-exports
    module GHC.TypeNats,
  )
where

import Data.Coerce (coerce)
import Data.Proxy (Proxy)
import Data.Type.Equality
  ( TestEquality (..),
    gcastWith,
    type (:~:) (..),
    type (==),
  )
import Data.Type.Natural.Utils
import GHC.Exts (Proxy#, proxy#)
import GHC.TypeNats
import Math.NumberTheory.Logarithms (naturalLog2)
import Numeric.Natural (Natural)
import Type.Reflection (Typeable)
import Unsafe.Coerce (unsafeCoerce)

-- | A singleton for type-level naturals
newtype SNat (n :: Nat) = SNat Natural
  deriving newtype (Show, Eq, Ord)

withKnownNat :: forall n r. SNat n -> (KnownNat n => r) -> r
withKnownNat (SNat n) act =
  case someNatVal n of
    SomeNat (_ :: Proxy m) ->
      gcastWith (unsafeCoerce (Refl @()) :: n :~: m) act

(%+) :: SNat n -> SNat m -> SNat (n + m)
(%+) = coerce $ (+) @Natural

(%-) :: SNat n -> SNat m -> SNat (n - m)
(%-) = coerce $ (-) @Natural

(%*) :: SNat n -> SNat m -> SNat (n * m)
(%*) = coerce $ (*) @Natural

sDiv :: SNat n -> SNat m -> SNat (Div n m)
sDiv = coerce $ div @Natural

sMod :: SNat n -> SNat m -> SNat (Mod n m)
sMod = coerce $ mod @Natural

(%^) :: SNat n -> SNat m -> SNat (n ^ m)
(%^) = coerce $ (^) @Natural @Natural

sLog2 :: SNat n -> SNat (Log2 n)
sLog2 = coerce $ fromIntegral @Int @Natural . naturalLog2

sNat :: forall n. KnownNat n => SNat n
sNat = SNat $ natVal' (proxy# :: Proxy# n)

infixl 6 %+, %-

infixl 7 %*, `sDiv`, `sMod`

infixr 8 %^

instance TestEquality SNat where
  testEquality (SNat l) (SNat r) =
    if l == r
      then Just trustMe
      else Nothing

-- | Since 1.1.0.0 (Type changed)
data Equality n m where
  Equal :: ((n == n) ~ 'True) => Equality n n
  NonEqual ::
    ((n === m) ~ 'False, (n == m) ~ 'False) =>
    Equality n m

equalAbsurdFromBool ::
  (x === y) ~ 'False => x :~: y -> a
equalAbsurdFromBool = \case {}

type family a === b where
  a === a = 'True
  _ === _ = 'False

infix 4 ===, %~

(%~) :: SNat l -> SNat r -> Equality l r
SNat l %~ SNat r =
  if l == r
    then unsafeCoerce (Equal @())
    else unsafeCoerce (NonEqual @0 @1)

type Zero = 0

type One = 1

sZero :: SNat 0
sZero = sNat

sOne :: SNat 1
sOne = sNat

type Succ n = n + 1

type S n = Succ n

sSucc, sS :: SNat n -> SNat (Succ n)
sS = (%+ sOne)
sSucc = sS

sPred :: SNat n -> SNat (Pred n)
sPred = (%- sOne)

type Pred n = n - 1

data ZeroOrSucc n where
  IsZero :: ZeroOrSucc 0
  IsSucc ::
    SNat n ->
    ZeroOrSucc (n + 1)

pattern Zero :: forall n. () => n ~ 0 => SNat n
pattern Zero <-
  (viewNat -> IsZero)
  where
    Zero = sZero

pattern Succ :: forall n. () => forall n1. n ~ Succ n1 => SNat n1 -> SNat n
pattern Succ n <-
  (viewNat -> IsSucc n)
  where
    Succ n = sSucc n

{-# COMPLETE Zero, Succ #-}

viewNat :: forall n. SNat n -> ZeroOrSucc n
viewNat n =
  case n %~ sNat @0 of
    Equal -> IsZero
    NonEqual -> IsSucc (sPred n)

type family FlipOrdering ord where
  FlipOrdering 'LT = 'GT
  FlipOrdering 'GT = 'LT
  FlipOrdering 'EQ = 'EQ

sFlipOrdering :: SOrdering ord -> SOrdering (FlipOrdering ord)
sFlipOrdering SLT = SGT
sFlipOrdering SEQ = SEQ
sFlipOrdering SGT = SLT

data SOrdering (ord :: Ordering) where
  SLT :: SOrdering 'LT
  SEQ :: SOrdering 'EQ
  SGT :: SOrdering 'GT

deriving instance Show (SOrdering ord)

deriving instance Eq (SOrdering ord)

deriving instance Typeable SOrdering

data SBool (b :: Bool) where
  SFalse :: SBool 'False
  STrue :: SBool 'True

deriving instance Show (SBool ord)

deriving instance Eq (SBool ord)

deriving instance Typeable SBool

infix 4 %<=?

(%<=?) :: SNat n -> SNat m -> SBool (n <=? m)
SNat n %<=? SNat m =
  if n <= m
    then unsafeCoerce STrue
    else unsafeCoerce SFalse

sCmpNat, sCompare :: SNat n -> SNat m -> SOrdering (CmpNat n m)
sCompare = sCmpNat
sCmpNat (SNat n) (SNat m) =
  case compare n m of
    LT -> unsafeCoerce SLT
    EQ -> unsafeCoerce SEQ
    GT -> unsafeCoerce SGT
