{-# LANGUAGE CPP, DataKinds, DeriveDataTypeable, EmptyCase, EmptyDataDecls #-}
{-# LANGUAGE ExplicitNamespaces, FlexibleContexts, FlexibleInstances       #-}
{-# LANGUAGE GADTs, KindSignatures, LambdaCase, PatternSynonyms, PolyKinds #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneDeriving           #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeInType, TypeOperators      #-}
{-# LANGUAGE ViewPatterns                                                  #-}
-- | Set-theoretic ordinals for general peano arithmetic models
module Data.Type.Ordinal
       ( -- * Data-types
         Ordinal (..), pattern OZ, pattern OS, HasOrdinal,
         -- * Quasi Quoter
         -- $quasiquotes
         mkOrdinalQQ, odPN, odLit,
         -- * Conversion from cardinals to ordinals.
         sNatToOrd', sNatToOrd, ordToInt, ordToSing,
         unsafeFromInt, inclusion, inclusion',
         -- * Ordinal arithmetics
         (@+), enumOrdinal,
         -- * Elimination rules for @'Ordinal' 'Z'@.
         absurdOrd, vacuousOrd
       ) where
import           Data.Kind
import           Data.List                    (genericDrop, genericTake)
import           Data.Ord                     (comparing)
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.Enum
import           Data.Type.Equality
import           Data.Type.Monomorphic
import qualified Data.Type.Natural            as PN
import           Data.Type.Natural.Builtin    ()
import           Data.Type.Natural.Class
import           Data.Typeable                (Typeable)
import           Data.Void                    (absurd)
import           GHC.TypeLits                 (type (+))
import qualified GHC.TypeLits                 as TL
import           Language.Haskell.TH          hiding (Type)
import           Language.Haskell.TH.Quote
import           Proof.Equational
import           Proof.Propositional
import           Unsafe.Coerce

-- | Set-theoretic (finite) ordinals:
--
-- > n = {0, 1, ..., n-1}
--
-- So, @Ordinal n@ has exactly n inhabitants. Especially, @Ordinal 'Z@ is isomorphic to @Void@.
--
--   Since 0.6.0.0
data Ordinal (n :: nat) where
  OLt :: (IsPeano nat, (n :< m) ~ 'True) => Sing (n :: nat) -> Ordinal m

fromOLt :: forall nat n m. (PeanoOrder nat, (Succ n :< Succ m) ~ 'True, SingI m)
        => Sing (n :: nat) -> Ordinal m
fromOLt  n =
  withRefl (sym $ succLneqSucc n (sing :: Sing m)) $
  OLt n

-- | Pattern synonym representing the 0-th ordinal.
--
--   Since 0.6.0.0
pattern OZ :: forall nat (n :: nat). IsPeano nat
           => (Zero nat :< n) ~ 'True => Ordinal n
pattern OZ <- OLt Zero where
  OZ = OLt sZero

-- | Pattern synonym @'OS' n@ represents (n+1)-th ordinal.
--
--   Since 0.6.0.0
pattern OS :: forall nat (t :: nat). (PeanoOrder nat, SingI t)
            => (IsPeano nat)
            => Ordinal t -> Ordinal (Succ t)
pattern OS n <- OLt (Succ (fromOLt -> n)) where
  OS o = succOrd o

-- | Since 0.2.3.0
deriving instance Typeable Ordinal

-- |  Class synonym for Peano numerals with ordinals.
--
--  Since 0.5.0.0
class (PeanoOrder nat, Monomorphicable (Sing :: nat -> *),
       Integral (MonomorphicRep (Sing :: nat -> *)),
       Show (MonomorphicRep (Sing :: nat -> *))) => HasOrdinal nat
instance (PeanoOrder nat, Monomorphicable (Sing :: nat -> *),
       Integral (MonomorphicRep (Sing :: nat -> *)),
       Show (MonomorphicRep (Sing :: nat -> *))) => HasOrdinal nat

instance (HasOrdinal nat, SingI (n :: nat))
      => Num (Ordinal n) where
  {-# SPECIALISE instance SingI n => Num (Ordinal (n :: PN.Nat))  #-}
  {-# SPECIALISE instance SingI n => Num (Ordinal (n :: TL.Nat))  #-}
  _ + _ = error "Finite ordinal is not closed under addition."
  _ - _ = error "Ordinal subtraction is not defined"
  negate OZ = OZ
  negate _  = error "There are no negative oridnals!"
  OZ * _ = OZ
  _ * OZ = OZ
  _ * _  = error "Finite ordinal is not closed under multiplication"
  abs    = id
  signum = error "What does Ordinal sign mean?"
  fromInteger = unsafeFromInt' (Proxy :: Proxy nat) . fromInteger

-- deriving instance Read (Ordinal n) => Read (Ordinal (Succ n))
instance (SingI n, HasOrdinal nat)
        => Show (Ordinal (n :: nat)) where
  {-# SPECIALISE instance SingI n => Show (Ordinal (n :: PN.Nat))  #-}
  {-# SPECIALISE instance SingI n => Show (Ordinal (n :: TL.Nat))  #-}
  showsPrec d o = showChar '#' . showParen True (showsPrec d (ordToInt o) . showString " / " . showsPrec d (demote $ Monomorphic (sing :: Sing n)))

instance (HasOrdinal nat)
         => Eq (Ordinal (n :: nat)) where
  {-# SPECIALISE instance Eq (Ordinal (n :: PN.Nat))  #-}
  {-# SPECIALISE instance Eq (Ordinal (n :: TL.Nat))  #-}
  o == o' = ordToInt o == ordToInt o'

instance (HasOrdinal nat) => Ord (Ordinal (n :: nat)) where
  compare = comparing ordToInt

instance (HasOrdinal nat, SingI n)
      => Enum (Ordinal (n :: nat)) where
  fromEnum = fromIntegral . ordToInt
  toEnum   = unsafeFromInt' (Proxy :: Proxy nat) . fromIntegral
  enumFrom = enumFromOrd
  enumFromTo = enumFromToOrd

enumFromToOrd :: forall (n :: nat).
                 (HasOrdinal nat, SingI n)
              => Ordinal n -> Ordinal n -> [Ordinal n]
enumFromToOrd ok ol =
  let k = ordToInt ok
      l = ordToInt ol
  in genericTake (l - k + 1) $ enumFromOrd ok

enumFromOrd :: forall (n :: nat).
               (HasOrdinal nat, SingI n)
            => Ordinal n -> [Ordinal n]
enumFromOrd ord = genericDrop (ordToInt ord) $ enumOrdinal (sing :: Sing n)

-- | Enumerate all @'Ordinal'@s less than @n@.
enumOrdinal :: (PeanoOrder nat) => Sing (n :: nat) -> [Ordinal n]
enumOrdinal (Succ n) = withSingI n $
  withWitness (lneqZero n) $
      OLt sZero : map succOrd (enumOrdinal n)
enumOrdinal _ = []

succOrd :: forall (n :: nat). (PeanoOrder nat, SingI n) => Ordinal n -> Ordinal (Succ n)
succOrd (OLt n) =
  withRefl (succLneqSucc n (sing :: Sing n)) $
  OLt (sSucc n)
{-# INLINE succOrd #-}

instance SingI n => Bounded (Ordinal ('PN.S n)) where
  minBound = OLt PN.SZ

  maxBound =
    withWitness (leqRefl (sing :: Sing n)) $
    sNatToOrd (sing :: Sing n)

instance (SingI m, SingI n, n ~ (m + 1)) => Bounded (Ordinal n) where
  minBound =
    withWitness (lneqZero (sing :: Sing m)) $
    OLt (sing :: Sing 0)
  {-# INLINE minBound #-}
  maxBound =
    withWitness (lneqSucc (sing :: Sing m)) $
    sNatToOrd (sing :: Sing m)
  {-# INLINE maxBound #-}

unsafeFromInt :: forall (n :: nat). (HasOrdinal nat, SingI (n :: nat))
              => MonomorphicRep (Sing :: nat -> *) -> Ordinal n
unsafeFromInt n =
    case promote (n :: MonomorphicRep (Sing :: nat -> *)) of
      Monomorphic sn ->
           case sn %:< (sing :: Sing n) of
             STrue -> sNatToOrd' (sing :: Sing n) sn
             SFalse -> error "Bound over!"

unsafeFromInt' :: forall proxy (n :: nat). (HasOrdinal nat, SingI n)
              => proxy nat -> MonomorphicRep (Sing :: nat -> *) -> Ordinal n
unsafeFromInt' _ n =
    case promote (n :: MonomorphicRep (Sing :: nat -> *)) of
      Monomorphic sn ->
           case sn %:< (sing :: Sing n) of
             STrue -> sNatToOrd' (sing :: Sing n) sn
             SFalse -> error "Bound over!"

-- | 'sNatToOrd'' @n m@ injects @m@ as @Ordinal n@.
--
--   Since 0.5.0.0
sNatToOrd' :: (PeanoOrder nat, (m :< n) ~ 'True) => Sing (n :: nat) -> Sing m -> Ordinal n
sNatToOrd' _ m = OLt m
{-# INLINE sNatToOrd' #-}

-- | 'sNatToOrd'' with @n@ inferred.
sNatToOrd :: (PeanoOrder nat, SingI (n :: nat), (m :< n) ~ 'True) => Sing m -> Ordinal n
sNatToOrd = sNatToOrd' sing

-- | Convert @Ordinal n@ into monomorphic @Sing@
--
-- Since 0.5.0.0
ordToSing :: (PeanoOrder nat) => Ordinal (n :: nat) -> SomeSing nat
ordToSing (OLt n) = SomeSing n
{-# INLINE ordToSing #-}

-- | Convert ordinal into @Int@.
ordToInt :: (HasOrdinal nat, int ~ MonomorphicRep (Sing :: nat -> *))
         => Ordinal (n :: nat)
         -> int
ordToInt (OLt n) = demote $ Monomorphic n
{-# SPECIALISE ordToInt :: Ordinal (n :: PN.Nat) -> Integer #-}
{-# SPECIALISE ordToInt :: Ordinal (n :: TL.Nat) -> Integer #-}

-- | Inclusion function for ordinals.
--
--   Since 0.7.0.0 (constraint was weakened since last released)
inclusion' :: (n :<= m) ~ 'True => Sing m -> Ordinal n -> Ordinal m
inclusion' _ = unsafeCoerce
{-# INLINE inclusion' #-}

-- | Inclusion function for ordinals with codomain inferred.
--
--   Since 0.7.0.0 (constraint was weakened since last released)
inclusion :: ((n :<= m) ~ 'True) => Ordinal n -> Ordinal m
inclusion on = unsafeCoerce on
{-# INLINE inclusion #-}


-- | Ordinal addition.
(@+) :: forall n m. (PeanoOrder nat, SingI (n :: nat), SingI m)
     => Ordinal n -> Ordinal m -> Ordinal (n :+ m)
OLt k @+ OLt l =
  let (n, m) = (n :: Sing n, m :: Sing m)
  in withWitness (plusStrictMonotone k n l m Witness Witness) $ OLt $ k %:+ l

-- | Since @Ordinal 'Z@ is logically not inhabited, we can coerce it to any value.
--
-- Since 0.2.3.0
absurdOrd :: PeanoOrder nat => Ordinal (Zero nat) -> a
absurdOrd (OLt n) = absurd $ lneqZeroAbsurd n Witness

-- | @'absurdOrd'@ for value in 'Functor'.
--
--   Since 0.2.3.0
vacuousOrd :: (PeanoOrder nat, Functor f) => f (Ordinal (Zero nat)) -> f a
vacuousOrd = fmap absurdOrd

{-$quasiquotes #quasiquoters#

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

-- | Quasiquoter generator for ordinals
mkOrdinalQQ :: TypeQ -> QuasiQuoter
mkOrdinalQQ t =
  QuasiQuoter { quoteExp  = \s -> [| OLt $(quoteExp (mkSNatQQ t) s) |]
              , quoteType = error "No type quoter for Ordinals"
              , quotePat  = \s -> [p| OLt ((%~ $(quoteExp (mkSNatQQ t) s)) -> Proved Refl) |]
              , quoteDec  = error "No declaration quoter for Ordinals"
              }

odPN, odLit :: QuasiQuoter
-- | Quasiquoter for ordinal indexed by Peano numeral @'Data.Type.Natural.Nat'@.
odPN  = mkOrdinalQQ [t| PN.Nat |]
-- | Quasiquoter for ordinal indexed by built-in numeral @'GHC.TypeLits.Nat'@.
odLit = mkOrdinalQQ [t| TL.Nat |]
