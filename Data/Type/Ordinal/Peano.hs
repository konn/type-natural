{-# LANGUAGE DataKinds, ExplicitNamespaces, FlexibleInstances, GADTs    #-}
{-# LANGUAGE KindSignatures, PatternSynonyms, TypeInType, TypeOperators #-}
-- | Module providing the same API as 'Data.Type.Ordinal' but specialised to
--   peano numeral @'Nat'@.
--   
--   Since 0.7.0.0
module Data.Type.Ordinal.Peano
       ( -- * Data-types and pattern synonyms
         Ordinal, pattern OLt, pattern OZ, pattern OS,
         -- * Quasi Quoter
         -- $quasiquotes
         od,
         -- * Conversion from cardinals to ordinals.
         sNatToOrd', sNatToOrd, ordToInt,
         unsafeFromInt, inclusion, inclusion',
         -- * Ordinal arithmetics
         (@+), enumOrdinal,
         -- * Elimination rules for @'Ordinal' 'Z'@.
         absurdOrd, vacuousOrd
       ) where
import           Data.Kind
import           Data.Singletons.Prelude      (POrd (..), SingI, Sing (..))
import           Data.Singletons.Prelude.Enum (PEnum (..))
import qualified Data.Type.Ordinal            as O
import           Data.Type.Natural
import           Language.Haskell.TH.Quote    (QuasiQuoter)
import           Data.Type.Monomorphic

-- | Set-theoretic (finite) ordinals:
--
-- > n = {0, 1, ..., n-1}
--
-- So, @Ordinal n@ has exactly n inhabitants. So especially @Ordinal 'Z@ is isomorphic to @Void@.
-- This module exports a variant of polymorphic @'Data.Type.Ordinal.Ordinal'@
-- specialised to Peano numeral @'Nat'@.
--   
--   Since 0.7.0.0
type Ordinal (n :: Nat) = O.Ordinal n

-- | We provide specialised version of constructor @'O.OLt'@ as type synonym @'OLt'@.
--   In some case, GHC warns about incomplete pattern using pattern  @'OLt'@,
--   but it is due to the limitation of GHC's current exhaustiveness checker.
--   
--   Since 0.7.0.0
pattern OLt :: () => forall  (n1 :: Nat). ((n1 :< t) ~ 'True)
            => Sing n1 -> O.Ordinal t
pattern OLt n = O.OLt n

-- | Pattern synonym representing the 0-th ordinal.
--   
--   Since 0.7.0.0
pattern OZ :: forall  (n :: Nat). ()
           => ('Z :< n) ~ 'True => O.Ordinal n
pattern OZ = O.OZ

-- | Pattern synonym @'OS' n@ represents (n+1)-th ordinal.
--   
--   Since 0.7.0.0
pattern OS :: forall (t :: Nat). (SingI t)
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

-- | Quasiquoter for ordinal indexed by Peano numeral @'Data.Type.Natural.Nat'@.
--   
--   Since 0.7.0.0
od :: QuasiQuoter
od = O.odLit
{-# INLINE od #-}

-- | 'sNatToOrd'' @n m@ injects @m@ as @Ordinal n@.
--   
--   Since 0.7.0.0
sNatToOrd' :: (m :< n) ~ 'True => Sing n -> Sing m -> Ordinal n
sNatToOrd' = O.sNatToOrd'
{-# INLINE sNatToOrd' #-}

-- | 'sNatToOrd'' with @n@ inferred.
--   
--   Since 0.7.0.0
sNatToOrd :: (SingI n, (m :< n) ~ 'True) => Sing m -> Ordinal n
sNatToOrd = O.sNatToOrd
{-# INLINE sNatToOrd #-}

-- | Convert ordinal into @Int@.
--   
--   Since 0.7.0.0
ordToInt :: Ordinal n -> Integer
ordToInt = O.ordToInt
{-# INLINE ordToInt #-}

unsafeFromInt :: SingI n
              => MonomorphicRep (Sing :: Nat -> Type) -> Ordinal n
unsafeFromInt = O.unsafeFromInt
{-# INLINE unsafeFromInt #-}

-- | Inclusion function for ordinals.
--
--   Since 0.7.0.0
inclusion :: (n :<= m) ~ 'True => Ordinal n -> Ordinal m
inclusion = O.inclusion
{-# INLINE inclusion #-}

-- | Inclusion function for ordinals with codomain inferred.
--
--   Since 0.7.0.0
inclusion' :: (n :<= m) ~ 'True => Sing m -> Ordinal n -> Ordinal m
inclusion' = O.inclusion'
{-# INLINE inclusion' #-}

-- | Ordinal addition.
--
--   Since 0.7.0.0
(@+) :: (SingI n, SingI m) => Ordinal n -> Ordinal m -> Ordinal (n :+ m)
(@+) = (O.@+)
{-# INLINE (@+) #-}

-- | Enumerate all @'Ordinal'@s less than @n@.
--
--   Since 0.7.0.0
enumOrdinal :: Sing n -> [Ordinal n]
enumOrdinal = O.enumOrdinal
{-# INLINE enumOrdinal #-}

-- | Since @Ordinal 'Z@ is logically not inhabited, we can coerce it to any value.
--
--   Since 0.7.0.0
absurdOrd :: Ordinal 'Z -> a
absurdOrd = O.absurdOrd
{-# INLINE absurdOrd #-}

-- | @'absurdOrd'@ for values in 'Functor'.
--
--   Since 0.7.0.0
vacuousOrd :: Functor f => f (Ordinal 'Z) -> f a
vacuousOrd = O.vacuousOrd
{-# INLINE vacuousOrd #-}
