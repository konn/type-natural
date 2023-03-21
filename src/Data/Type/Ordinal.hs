{-# LANGUAGE DataKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin Data.Type.Natural.Presburger.MinMaxSolver #-}
{-# OPTIONS_GHC -fobject-code #-}

{- | Set-theoretic ordinals for built-in type-level naturals

  Since 1.0.0.0
-}
module Data.Type.Ordinal
  ( -- * Data-types
    Ordinal (..),
    pattern OZ,
    pattern OS,

    -- * Quasi Quoter
    -- $quasiquotes
    od,

    -- * Conversion from cardinals to ordinals.
    sNatToOrd',
    sNatToOrd,
    ordToNatural,
    unsafeNaturalToOrd',
    unsafeNaturalToOrd,
    reallyUnsafeNaturalToOrd,
    naturalToOrd,
    naturalToOrd',
    ordToSNat,
    inclusion,
    inclusion',

    -- * Ordinal arithmetics
    (@+),
    enumOrdinal,

    -- * Elimination rules for @'Ordinal' 'Z'@.
    absurdOrd,
    vacuousOrd,
  )
where

import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality
import Data.Type.Natural
import Data.Typeable (Typeable)
import Language.Haskell.TH.Quote
import Numeric.Natural ( Natural )
import Unsafe.Coerce
import Proof.Propositional (IsTrue (Witness))
import Data.Type.Natural.Lemma.Order (lneqZeroAbsurd)
import Data.Void (absurd)

{- | Set-theoretic (finite) ordinals:

 > n = {0, 1, ..., n-1}

 So, @Ordinal n@ has exactly n inhabitants. So especially @Ordinal 'Z@ is isomorphic to @Void@.

   Since 1.0.0.0
-}
data Ordinal (n :: Nat) where
  OLt :: (n < m) => SNat (n :: Nat) -> Ordinal m

{-# COMPLETE OLt #-}

fromOLt ::
  forall n m.
  ((Succ n < Succ m), KnownNat m) =>
  SNat (n :: Nat) ->
  Ordinal m
fromOLt n = OLt n

{- | Pattern synonym representing the 0-th ordinal.

   Since 1.0.0.0
-}
pattern OZ :: forall (n :: Nat). (0 < n) => Ordinal n
pattern OZ <- OLt Zero where OZ = OLt sZero

{- | Pattern synonym @'OS' n@ represents (n+1)-th ordinal.

   Since 1.0.0.0
-}
pattern OS :: forall (t :: Nat). (KnownNat t) => Ordinal t -> Ordinal (Succ t)
pattern OS n <-
  OLt (Succ (fromOLt -> n))
  where
    OS o = succOrd o

-- | Since 1.0.0.0
deriving instance Typeable Ordinal

{- |  Class synonym for Peano numerals with ordinals.

  Since 1.0.0.0
-}
instance (KnownNat n) => Num (Ordinal n) where
  _ + _ = error "Finite ordinal is not closed under addition."
  _ - _ = error "Ordinal subtraction is not defined"
  negate _ = error "There are no negative oridnals!"
  _ * _ = error "Finite ordinal is not closed under multiplication"
  abs = id
  signum = error "What does Ordinal sign mean?"
  fromInteger = unsafeFromNatural' . fromIntegral

unsafeFromNatural' :: forall n. KnownNat n => Natural -> Ordinal n
unsafeFromNatural' k = withSNat k $ \sk ->
  case sk %<? sNat @n of
    STrue -> OLt sk
    SFalse -> error $ "Index out of bounds: " ++ show (k, natVal @n Proxy)

-- deriving instance Read (Ordinal n) => Read (Ordinal (Succ n))
instance
  (KnownNat n) =>
  Show (Ordinal (n :: Nat))
  where
  showsPrec d o = showChar '#' . showParen True (showsPrec d (ordToNatural o) . showString " / " . showsPrec d (fromSNat (sNat :: SNat n)))

instance Eq (Ordinal (n :: Nat)) where
  o == o' = ordToNatural o == ordToNatural o'

instance Ord (Ordinal (n :: Nat)) where
  compare = comparing ordToNatural

instance
  (KnownNat n) =>
  Enum (Ordinal (n :: Nat))
  where
  fromEnum = fromEnum . ordToNatural
  toEnum = unsafeFromNatural' . fromIntegral
  enumFrom = enumFromOrd
  enumFromTo = enumFromToOrd

-- | Since 1.0.0.0 (type changed)
enumFromToOrd ::
  forall (n :: Nat).
  (KnownNat n) =>
  Ordinal n ->
  Ordinal n ->
  [Ordinal n]
enumFromToOrd ok ol =
  map
    (reallyUnsafeNaturalToOrd $ sNat @n)
    [ordToNatural ok .. ordToNatural ol]

-- | Since 1.0.0.0 (type changed)
enumFromOrd ::
  forall (n :: Nat).
  (KnownNat n) =>
  Ordinal n ->
  [Ordinal n]
enumFromOrd ord =
  map
    (reallyUnsafeNaturalToOrd Proxy)
    [ordToNatural ord .. natVal @n Proxy - 1]

-- | Enumerate all @'Ordinal'@s less than @n@.
enumOrdinal :: SNat (n :: Nat) -> [Ordinal n]
enumOrdinal sn = withKnownNat sn $ map (reallyUnsafeNaturalToOrd Proxy) [0 .. fromSNat sn - 1]

-- | Since 1.0.0.0 (type changed)
succOrd :: forall (n :: Nat). (KnownNat n) => Ordinal n -> Ordinal (Succ n)
succOrd (OLt k) = OLt (sSucc k)
{-# INLINE succOrd #-}

instance (KnownNat n, 0 < n) => Bounded (Ordinal n) where
  minBound = OLt sZero

  maxBound = withKnownNat (sNat @n %- sNat @1) $ OLt $ sNat @(n - 1)

{- | Converts @'Natural'@s into @'Ordinal n'@.
   If the given natural is greater or equal to @n@, raises exception.

   Since 1.0.0.0
-}
unsafeNaturalToOrd ::
  forall (n :: Nat).
  (KnownNat n) =>
  Natural ->
  Ordinal n
unsafeNaturalToOrd k =
  fromMaybe (error "unsafeNaturalToOrd Out of bound") $
    naturalToOrd k

-- | Since 1.0.0.0
unsafeNaturalToOrd' ::
  forall proxy (n :: Nat).
  (KnownNat n) =>
  proxy n ->
  Natural ->
  Ordinal n
unsafeNaturalToOrd' _ = unsafeNaturalToOrd

{-# WARNING reallyUnsafeNaturalToOrd "This function may violate type safety. Use with care!" #-}

{- | Converts @'Natural'@s into @'Ordinal' n@, WITHOUT any boundary check.
   This function may easily violate type-safety. Use with care!
-}
reallyUnsafeNaturalToOrd ::
  forall pxy (n :: Nat).
  (KnownNat n) =>
  pxy ->
  Natural ->
  Ordinal n
reallyUnsafeNaturalToOrd _ k =
  withSNat k $ \(sk :: SNat k) ->
    gcastWith (unsafeCoerce (Refl :: () :~: ()) :: (k <? n) :~: 'True) $
      OLt sk

{- | 'sNatToOrd'' @n m@ injects @m@ as @Ordinal n@.

   Since 1.0.0.0
-}
sNatToOrd' :: (m < n) => SNat (n :: Nat) -> SNat m -> Ordinal n
sNatToOrd' _ = OLt
{-# INLINE sNatToOrd' #-}

-- | 'sNatToOrd'' with @n@ inferred.
sNatToOrd :: (KnownNat n, m < n) => SNat m -> Ordinal n
sNatToOrd = sNatToOrd' sNat

-- | Since 1.0.0.0
naturalToOrd ::
  forall n.
  (KnownNat n) =>
  Natural ->
  Maybe (Ordinal (n :: Nat))
naturalToOrd = naturalToOrd' (sNat :: SNat n)

naturalToOrd' ::
  SNat (n :: Nat) ->
  Natural ->
  Maybe (Ordinal n)
naturalToOrd' sn k = withSNat k $ \(sk :: SNat pk) ->
  case sk %<? sn of
    STrue -> Just (OLt sk)
    _ -> Nothing

{- | Convert @Ordinal n@ into monomorphic @SNat@

 Since 1.0.0.0
-}
ordToSNat :: Ordinal (n :: Nat) -> SomeSNat
ordToSNat (OLt n) = withKnownNat n $ SomeSNat n
{-# INLINE ordToSNat #-}

ordToNatural ::
  Ordinal (n :: Nat) ->
  Natural
ordToNatural (OLt n) = fromSNat n

{- | Inclusion function for ordinals.

   Since 1.0.0.0(constraint was weakened since last released)
-}
inclusion' :: (n <= m) => SNat m -> Ordinal n -> Ordinal m
inclusion' _ = unsafeCoerce
{-# INLINE inclusion' #-}

{- | Inclusion function for ordinals with codomain inferred.

   Since 1.0.0.0(constraint was weakened since last released)
-}
inclusion :: (n <= m) => Ordinal n -> Ordinal m
inclusion (OLt a) = OLt a
{-# INLINE inclusion #-}

{- | Ordinal addition.

   Since 1.0.0.0(type changed)
-}
(@+) ::
  forall (n :: Nat) m.
  (KnownNat n, KnownNat m) =>
  Ordinal n ->
  Ordinal m ->
  Ordinal (n + m)
OLt k @+ OLt l = OLt $ k %+ l

{- | Since @Ordinal 'Z@ is logically not inhabited, we can coerce it to any value.

 Since 1.0.0.0
-}
absurdOrd :: Ordinal 0 -> a
absurdOrd (OLt sn) = absurd $ lneqZeroAbsurd sn Witness

{- | @'absurdOrd'@ for value in 'Functor'.

   Since 1.0.0.0
-}
vacuousOrd :: (Functor f) => f (Ordinal 0) -> f a
vacuousOrd = fmap absurdOrd

{- $quasiquotes #quasiquoters#

   This section provides QuasiQuoter and general generator for ordinals.
   Note that, @'Num'@ instance for @'Ordinal'@s DOES NOT
   checks boundary; with @'od'@, we can use literal with
   boundary check.
   For example, with @-XQuasiQuotes@ language extension enabled,
   @['od'| 12 |] :: Ordinal 1@ doesn't typechecks and causes compile-time error,
   whilst @12 :: Ordinal 1@ compiles but raises run-time error.
   So, to enforce correctness, we recommend to use these quoters
   instead of bare @'Num'@ numerals.
-}

-- | Quasiquoter for ordinal indexed by built-in numeral @'GHC.TypeLits.Nat'@.
od :: QuasiQuoter
od =
  QuasiQuoter
    { quoteExp = \s -> [|OLt $(quoteExp snat s)|]
    , quoteType = error "No type quoter for Ordinals"
    , quotePat = \s -> [p|OLt ((%~ $(quoteExp snat s)) -> Equal)|]
    , quoteDec = error "No declaration quoter for Ordinals"
    }

-- >>> 42
