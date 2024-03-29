{-# LANGUAGE CPP #-}
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
  ( SNat (Zero, Succ),
#if !MIN_VERSION_base(4,18,0)
    fromSNat,
    withKnownNat,
    withSomeSNat,
#endif
    unsafeLiftSBin,
    ZeroOrSucc (..),
    viewNat,
    sNat,
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
    Natural,
    OrderingI(..),
    fromOrderingI,
    toOrderingI,
    -- Re-exports
    module GHC.TypeNats,
  )
where

import Data.Type.Equality
  ( type (:~:) (..),
    type (==),
  )
import GHC.TypeNats
import Math.NumberTheory.Logarithms (naturalLog2)
import Type.Reflection (Typeable)
import Unsafe.Coerce (unsafeCoerce)
import Numeric.Natural

#if MIN_VERSION_base(4,16,0)
import Data.Type.Ord (OrderingI(..))
#endif

#if !MIN_VERSION_base(4,18,0)
import Data.Proxy
import Data.Type.Equality
import GHC.Exts
#endif

#if !MIN_VERSION_base(4,18,0)
-- | A singleton for type-level naturals
newtype SNat (n :: Nat) = UnsafeSNat Natural
  deriving newtype (Show, Eq, Ord)

fromSNat :: SNat n -> Natural
fromSNat = coerce

withKnownNat :: forall n rep (r :: TYPE rep). SNat n -> (KnownNat n => r) -> r
withKnownNat (UnsafeSNat n) act =
  case someNatVal n of
    SomeNat (_ :: Proxy m) ->
      case unsafeCoerce (Refl @()) :: n :~: m of
        Refl -> act

data KnownNatInstance (n :: Nat) where
  KnownNatInstance :: KnownNat n => KnownNatInstance n

-- An internal function that is only used for defining the SNat pattern
-- synonym.
knownNatInstance :: SNat n -> KnownNatInstance n
knownNatInstance sn = withKnownNat sn KnownNatInstance

pattern SNat :: forall n. () => KnownNat n => SNat n
pattern SNat <- (knownNatInstance -> KnownNatInstance) 
  where SNat = sNat

withSomeSNat :: forall rep (r :: TYPE rep). Natural -> (forall n. SNat n -> r) -> r
withSomeSNat n f = f (UnsafeSNat n)
#endif

unsafeLiftSBin :: (Natural -> Natural -> Natural) -> SNat n -> SNat m -> SNat k
{-# INLINE unsafeLiftSBin #-}
unsafeLiftSBin f = \l r -> withSomeSNat (fromSNat l `f` fromSNat r) unsafeCoerce

unsafeLiftSUnary :: (Natural -> Natural) -> SNat n -> SNat k
{-# INLINE unsafeLiftSUnary #-}
unsafeLiftSUnary f = \l -> withSomeSNat (f $ fromSNat l) unsafeCoerce

(%+) :: SNat n -> SNat m -> SNat (n + m)
{-# INLINE (%+) #-}
(%+) = unsafeLiftSBin (+)

(%-) :: SNat n -> SNat m -> SNat (n - m)
(%-) = unsafeLiftSBin (-)

(%*) :: SNat n -> SNat m -> SNat (n * m)
(%*) = unsafeLiftSBin (*)

sDiv :: SNat n -> SNat m -> SNat (Div n m)
sDiv = unsafeLiftSBin quot

sMod :: SNat n -> SNat m -> SNat (Mod n m)
sMod = unsafeLiftSBin rem

(%^) :: SNat n -> SNat m -> SNat (n ^ m)
(%^) = unsafeLiftSBin (^)

sLog2 :: SNat n -> SNat (Log2 n)
sLog2 = unsafeLiftSUnary $ fromIntegral . naturalLog2

sNat :: forall n. KnownNat n => SNat n
#if MIN_VERSION_base(4,18,0)
sNat = SNat
#else
sNat = UnsafeSNat $ natVal' (proxy# :: Proxy# n)
#endif


infixl 6 %+, %-

infixl 7 %*, `sDiv`, `sMod`

infixr 8 %^

#if !MIN_VERSION_ghc(4,18,0)
instance TestEquality SNat where
  testEquality (UnsafeSNat l) (UnsafeSNat r) =
    if l == r
      then Just trustMe
      else Nothing
#endif


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
l %~ r =
  if fromSNat l == fromSNat r
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


#if !MIN_VERSION_base(4,16,0)
data OrderingI (a :: Nat) (b :: Nat) where
  LTI :: CmpNat a b ~ 'LT => OrderingI a b
  EQI :: CmpNat a b ~ 'EQ => OrderingI a b
  GTI :: CmpNat a b ~ 'GT => OrderingI a b
#endif

type family FlipOrdering ord where
  FlipOrdering 'LT = 'GT
  FlipOrdering 'GT = 'LT
  FlipOrdering 'EQ = 'EQ

data SOrdering (ord :: Ordering) where
  SLT :: SOrdering 'LT
  SEQ :: SOrdering 'EQ
  SGT :: SOrdering 'GT

fromOrderingI :: OrderingI n m -> SOrdering (CmpNat n m)
fromOrderingI LTI = SLT
fromOrderingI EQI = SEQ
fromOrderingI GTI = SGT

toOrderingI :: SOrdering (CmpNat n m) -> OrderingI n m
toOrderingI SLT = LTI
toOrderingI SEQ = EQI
toOrderingI SGT = GTI

deriving instance Show (SOrdering ord)

deriving instance Eq (SOrdering ord)

deriving instance Typeable SOrdering

sFlipOrdering :: SOrdering ord -> SOrdering (FlipOrdering ord)
sFlipOrdering SLT = SGT
sFlipOrdering SEQ = SEQ
sFlipOrdering SGT = SLT

data SBool (b :: Bool) where
  SFalse :: SBool 'False
  STrue :: SBool 'True

deriving instance Show (SBool ord)

deriving instance Eq (SBool ord)

deriving instance Typeable SBool

infix 4 %<=?

(%<=?) :: SNat n -> SNat m -> SBool (n <=? m)
n %<=? m =
  if fromSNat n <= fromSNat m
    then unsafeCoerce STrue
    else unsafeCoerce SFalse

sCmpNat, sCompare :: SNat n -> SNat m -> SOrdering (CmpNat n m)
sCompare = sCmpNat
sCmpNat n m =
  case compare (fromSNat n) (fromSNat m) of
    LT -> unsafeCoerce SLT
    EQ -> unsafeCoerce SEQ
    GT -> unsafeCoerce SGT

