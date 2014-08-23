{-# LANGUAGE CPP, DataKinds, EmptyDataDecls, FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances, GADTs, KindSignatures, PolyKinds      #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TemplateHaskell #-}
{-# LANGUAGE TypeFamilies, TypeOperators                              #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE EmptyCase, LambdaCase #-}
#endif
-- | Set-theoretic ordinal arithmetic
module Data.Type.Ordinal
       ( -- * Data-types
         Ordinal (..),
         -- * Conversion from cardinals to ordinals.
         sNatToOrd', sNatToOrd, ordToInt, ordToSNat,
         ordToSNat', CastedOrdinal(..),
         unsafeFromInt, inclusion, inclusion',
         -- * Ordinal arithmetics
         (@+), enumOrdinal,
         -- * Elimination rules for @'Ordinal' 'Z'@.
         absurdOrd, vacuousOrd, vacuousOrdM,
         -- * Quasi Quoter
         od
       ) where
import Data.Constraint
import Data.Type.Monomorphic
import Data.Type.Natural         hiding (promote)
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Proof.Equational          (coerce)
import Unsafe.Coerce
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
import Data.Singletons.Prelude
#endif
import Control.Monad (liftM)

-- | Set-theoretic (finite) ordinals:
--
-- > n = {0, 1, ..., n-1}
--
-- So, @Ordinal n@ has exactly n inhabitants. So especially @Ordinal Z@ is isomorphic to @Void@.
data Ordinal n where
  OZ :: Ordinal (S n)
  OS :: Ordinal n -> Ordinal (S n)

-- | Parsing always fails, because there are no inhabitant.
instance Read (Ordinal Z) where
  readsPrec _ _ = []

instance SingI n => Num (Ordinal n) where
  _ + _ = error "Finite ordinal is not closed under addition."
  _ - _ = error "Ordinal subtraction is not defined"
  negate OZ = OZ
  negate _  = error "There are no negative oridnals!"
  OZ * _ = OZ
  _ * OZ = OZ
  _ * _  = error "Finite ordinal is not closed under multiplication"
  abs    = id
  signum = error "What does Ordinal sign mean?"
  fromInteger = unsafeFromInt . fromInteger

deriving instance Read (Ordinal n) => Read (Ordinal (S n))
deriving instance Show (Ordinal n)
deriving instance Eq (Ordinal n)
deriving instance Ord (Ordinal n)

instance SingI n => Enum (Ordinal n) where
  fromEnum = ordToInt
  toEnum   = unsafeFromInt
  enumFrom = enumFromOrd
  enumFromTo = enumFromToOrd

enumFromToOrd :: forall n. SingI n => Ordinal n -> Ordinal n -> [Ordinal n]
enumFromToOrd ok ol =
  let k = ordToInt ok
      l = ordToInt ol
  in take (l - k + 1) $ enumFromOrd ok

enumFromOrd :: forall n. SingI n => Ordinal n -> [Ordinal n]
enumFromOrd ord = drop (ordToInt ord) $ enumOrdinal (sing :: SNat n)

enumOrdinal :: SNat n -> [Ordinal n]
enumOrdinal SZ = []
enumOrdinal (SS n) = OZ : map OS (enumOrdinal n)

instance SingI n => Bounded (Ordinal (S n)) where
  minBound = OZ
  maxBound =
    case propToBoolLeq $ leqRefl (sing :: SNat n) of
      Dict -> sNatToOrd (sing :: SNat n)

unsafeFromInt :: forall n. SingI n => Int -> Ordinal n
unsafeFromInt n =
    case (promote n :: Monomorphic (Sing :: Nat -> *)) of
      Monomorphic sn ->
        case SS sn %:<<= (sing :: SNat n) of
          STrue -> sNatToOrd' (sing :: SNat n) sn
          SFalse -> error "Bound over!"

-- | 'sNatToOrd'' @n m@ injects @m@ as @Ordinal n@.
sNatToOrd' :: (S m :<<= n) ~ True => SNat n -> SNat m -> Ordinal n
sNatToOrd' (SS _) SZ = OZ
sNatToOrd' (SS n) (SS m) = OS $ sNatToOrd' n m
sNatToOrd' _ _ = bugInGHC

-- | 'sNatToOrd'' with @n@ inferred.
sNatToOrd :: (SingI n, (S m :<<= n) ~ True) => SNat m -> Ordinal n
sNatToOrd = sNatToOrd' sing

data CastedOrdinal n where
  CastedOrdinal :: (S m :<<= n) ~ True => SNat m -> CastedOrdinal n

-- | Convert @Ordinal n@ into @SNat m@ with the proof of @S m :<<= n@.
ordToSNat' :: Ordinal n -> CastedOrdinal n
ordToSNat' OZ = CastedOrdinal SZ
ordToSNat' (OS on) =
  case ordToSNat' on of
    CastedOrdinal m -> CastedOrdinal (SS m)

-- | Convert @Ordinal n@ into monomorphic @SNat@
ordToSNat :: Ordinal n -> Monomorphic (Sing :: Nat -> *)
ordToSNat OZ = Monomorphic SZ
ordToSNat (OS n) =
  case ordToSNat n of
    Monomorphic sn ->
      case singInstance sn of
        SingInstance -> Monomorphic (SS sn)

-- | Convert ordinal into @Int@.
ordToInt :: Ordinal n -> Int
ordToInt OZ = 0
ordToInt (OS n) = 1 + ordToInt n

-- | Inclusion function for ordinals.
inclusion' :: (n :<<= m) ~ True => SNat m -> Ordinal n -> Ordinal m
inclusion' _ = unsafeCoerce
{-# INLINE inclusion' #-}
{-
-- The "proof" of the correctness of the above
inclusion' :: (n :<<= m) ~ True => SNat m -> Ordinal n -> Ordinal m
inclusion' (SS SZ) OZ = OZ
inclusion' (SS (SS _)) OZ = OZ
inclusion' (SS (SS n)) (OS m) = OS $ inclusion' (SS n) m
inclusion' _ _ = bugInGHC
-}

-- | Inclusion function for ordinals with codomain inferred.
inclusion :: ((n :<<= m) ~ True) => Ordinal n -> Ordinal m
inclusion on = unsafeCoerce on
{-# INLINE inclusion #-}

-- | Ordinal addition.
(@+) :: forall n m. (SingI n, SingI m) => Ordinal n -> Ordinal m -> Ordinal (n :+ m)
OZ @+ n =
  let sn = sing :: SNat n
      sm = sing :: SNat m
  in case propToBoolLeq (plusLeqR sn sm) of
      Dict -> inclusion n
OS n @+ m =
  case sing :: SNat n of
    SS sn -> case singInstance sn of SingInstance -> OS $ n @+ m
    _ -> bugInGHC

-- | Since @Ordinal Z@ is logically not inhabited, we can coerce it to any value.
--
-- Since 0.2.3.0
absurdOrd :: Ordinal Z -> a
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
absurdOrd cs = case cs of {}
#else
absurdOrd _ = error "Impossible!"
#endif

-- | 'absurdOrd' for the value in 'Functor'.
-- 
--   Since 0.2.3.0
vacuousOrd :: Functor f => f (Ordinal Z) -> f a
vacuousOrd = fmap absurdOrd

-- | 'absurdOrd' for the value in 'Monad'.
--   This function will become uneccesary once 'Applicative' (and hence 'Functor')
--   become the superclass of 'Monad'.
-- 
--   Since 0.2.3.0
vacuousOrdM :: Monad m => m (Ordinal Z) -> m a
vacuousOrdM = liftM absurdOrd

-- | Quasiquoter for ordinals
od :: QuasiQuoter
od = QuasiQuoter { quoteExp = foldr appE (conE 'OZ) . flip replicate (conE 'OS) . read
                 , quoteType = error "No type quoter for Ordinals"
                 , quotePat = foldr (\a b -> conP a [b]) (conP 'OZ []) . flip replicate 'OS . read
                 , quoteDec = error "No declaration quoter for Ordinals"
                 }
