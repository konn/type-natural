{-# LANGUAGE DataKinds, ExplicitNamespaces, FlexibleInstances, GADTs    #-}
{-# LANGUAGE KindSignatures, PatternSynonyms, TypeInType, TypeOperators #-}
{-# OPTIONS_GHC -Wno-warnings-deprecations #-}
-- | Module providing the same API as 'Data.Type.Ordinal' but specialised to
--   GHC's builtin @'Nat'@.
--   
--   Since 0.7.1.0
module Data.Type.Ordinal.Builtin
       ( -- * Data-types and pattern synonyms
         Ordinal, pattern OLt, pattern OZ, pattern OS,
         -- * Quasi Quoter
         -- $quasiquotes
         od,
         -- * Conversion from cardinals to ordinals.
         sNatToOrd', sNatToOrd, ordToNatural,
         unsafeNaturalToOrd, naturalToOrd, naturalToOrd',
         inclusion, inclusion',
         -- * Ordinal arithmetics
         (@+), enumOrdinal,
         -- * Elimination rules for @'Ordinal' 0'@.
         absurdOrd, vacuousOrd,
         -- * Deprecated combinators
         ordToInt, unsafeFromInt
       ) where
import qualified Data.Type.Natural.Singleton.Compat as SC

import Numeric.Natural (Natural)
import           Data.Singletons (SingI, Sing)
import           Data.Singletons.Prelude.Enum (PEnum (..))
import qualified Data.Type.Ordinal            as O
import           GHC.TypeLits
import           Language.Haskell.TH.Quote    (QuasiQuoter)

-- | Set-theoretic (finite) ordinals:
--
-- > n = {0, 1, ..., n-1}
--
-- So, @Ordinal n@ has exactly n inhabitants. So especially @Ordinal 0@ is isomorphic to @Void@.
-- This module exports a variant of polymorphic @'Data.Type.Ordinal.Ordinal'@
-- specialised to GHC's builtin numeral @'Nat'@.
--   
--   Since 0.7.0.0
type Ordinal (n :: Nat) = O.Ordinal n

-- | We provide specialised version of constructor @'O.OLt'@ as type synonym @'OLt'@.
--   In some case, GHC warns about incomplete pattern using pattern  @'OLt'@,
--   but it is due to the limitation of GHC's current exhaustiveness checker.
--   
--   Since 0.7.0.0
pattern OLt :: () => forall  (n1 :: Nat). ((n1 SC.< t) ~ 'True)
            => Sing n1 -> O.Ordinal t
pattern OLt n = O.OLt n
{-# COMPLETE OLt #-}

-- | Pattern synonym representing the 0-th ordinal.
--   
--   Since 0.7.0.0
pattern OZ :: forall  (n :: Nat). ()
           => (0 SC.< n) ~ 'True => O.Ordinal n
pattern OZ = O.OZ

-- | Pattern synonym @'OS' n@ represents (n+1)-th ordinal.
--   
--   Since 0.7.0.0
pattern OS :: forall (t :: Nat). (KnownNat t)
           => () => O.Ordinal t -> O.Ordinal (Succ t)
pattern OS n = O.OS n

{-$quasiquotes #quasiquoters#

   This section provides QuasiQuoter for ordinals.
   Note that, @'Num'@ instance for @'Ordinal'@s DOES NOT
   checks boundary; with @'od'@, we can use literal with
   boundary check.
   For example, with @-XQuasiQuotes@ language extension enabled,
   @['od'| 12 |] :: Ordinal 1@ doesn't typechecks and causes compile-time error,
   whilst @12 :: Ordinal 1@ compiles but raises run-time error.
   So, to enforce correctness, we recommend to use these quoters
   instead of bare @'Num'@ numerals.
-}

-- | Quasiquoter for ordinal indexed by GHC's built-n @'Data.Type.Natural.Nat'@.
--   
--   Since 0.7.0.0
od :: QuasiQuoter
od = O.odLit
{-# INLINE od #-}

-- | 'sNatToOrd'' @n m@ injects @m@ as @Ordinal n@.
--   
--   Since 0.7.0.0
sNatToOrd' :: (m SC.< n) ~ 'True => Sing n -> Sing m -> Ordinal n
sNatToOrd' = O.sNatToOrd'
{-# INLINE sNatToOrd' #-}

-- | 'sNatToOrd'' with @n@ inferred.
--   
--   Since 0.7.0.0
sNatToOrd :: (KnownNat n, (m SC.< n) ~ 'True) => Sing m -> Ordinal n
sNatToOrd = O.sNatToOrd
{-# INLINE sNatToOrd #-}

{-# DEPRECATED ordToInt "Use ordToNatural instead" #-}
-- | Convert ordinal into @Int@.
--   
--   Since 0.7.0.0
ordToInt :: Ordinal n -> Int
ordToInt = O.ordToInt
{-# INLINE ordToInt #-}

{-# DEPRECATED unsafeFromInt "Use unsafeNaturalToOrd instead" #-}
unsafeFromInt :: KnownNat n
              => Int -> Ordinal n
unsafeFromInt = O.unsafeFromInt
{-# INLINE unsafeFromInt #-}

ordToNatural :: Ordinal (n :: Nat) -> Natural
ordToNatural = O.ordToNatural
{-# INLINE ordToNatural #-}


naturalToOrd :: SingI (n :: Nat) => Natural -> Maybe (Ordinal n)
naturalToOrd = O.naturalToOrd
{-# INLINE naturalToOrd #-}

naturalToOrd' :: Sing (n :: Nat) -> Natural -> Maybe (Ordinal n)
naturalToOrd' = O.naturalToOrd'
{-# INLINE naturalToOrd' #-}

unsafeNaturalToOrd :: SingI (n :: Nat) => Natural -> Ordinal n
unsafeNaturalToOrd = O.unsafeNaturalToOrd
{-# INLINE unsafeNaturalToOrd #-}

-- | Inclusion function for ordinals.
--
--   Since 0.7.0.0
inclusion :: (n SC.<= m) ~ 'True => Ordinal n -> Ordinal m
inclusion = O.inclusion
{-# INLINE inclusion #-}

-- | Inclusion function for ordinals with codomain inferred.
--
--   Since 0.7.0.0
inclusion' :: (n SC.<= m) ~ 'True => Sing m -> Ordinal n -> Ordinal m
inclusion' = O.inclusion'
{-# INLINE inclusion' #-}

-- | Ordinal addition.
--
--   Since 0.7.0.0
(@+) :: (KnownNat n, KnownNat m) => Ordinal n -> Ordinal m -> Ordinal (n + m)
(@+) = (O.@+)
{-# INLINE (@+) #-}

-- | Enumerate all @'Ordinal'@s less than @n@.
--
--   Since 0.7.0.0
enumOrdinal :: Sing n -> [Ordinal n]
enumOrdinal = O.enumOrdinal
{-# INLINE enumOrdinal #-}

-- | Since @Ordinal 0@ is logically not inhabited, we can coerce it to any value.
--
--   Since 0.7.0.0
absurdOrd :: Ordinal 0 -> a
absurdOrd = O.absurdOrd
{-# INLINE absurdOrd #-}

-- | @'absurdOrd'@ for values in 'Functor'.
--
--   Since 0.7.0.0
vacuousOrd :: Functor f => f (Ordinal 0) -> f a
vacuousOrd = O.vacuousOrd
{-# INLINE vacuousOrd #-}
