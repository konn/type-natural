{-# LANGUAGE CPP, DataKinds, DeriveDataTypeable, EmptyCase, EmptyDataDecls #-}
{-# LANGUAGE ExplicitNamespaces, FlexibleContexts, FlexibleInstances       #-}
{-# LANGUAGE GADTs, KindSignatures, LambdaCase, PatternSynonyms, PolyKinds #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneDeriving           #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators                  #-}
-- | Set-theoretic ordinals for general peano arithmetic models
module Data.Type.Ordinal
       ( -- * Data-types
         Ordinal (..), HasOrdinal,
         -- * Conversion from cardinals to ordinals.
         sNatToOrd', sNatToOrd, ordToInt, ordToSing,
         ordToSing', CastedOrdinal(..),
         unsafeFromInt, inclusion, inclusion',
         -- * Ordinal arithmetics
         (@+), enumOrdinal,
         -- * Elimination rules for @'Ordinal' 'Z'@.
         absurdOrd, vacuousOrd, vacuousOrdM,
         -- * Quasi Quoter
         od
       ) where
import           Control.Monad                (liftM)
import           Data.List                    (genericDrop, genericTake)
import           Data.Ord                     (comparing)
import           Data.Singletons.Prelude
import           Data.Singletons.Prelude.Enum
import           Data.Type.Equality
import           Data.Type.Monomorphic
import qualified Data.Type.Natural            as PN
import           Data.Type.Natural.Builtin    ()
import           Data.Type.Natural.Class
import           Data.Typeable                (Typeable)
import           GHC.TypeLits                 (type (+))
import qualified GHC.TypeLits                 as TL
import           Language.Haskell.TH          hiding (Type)
import           Language.Haskell.TH.Quote
import           Proof.Equational
import           Proof.Propositional
import           Unsafe.Coerce
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
import Data.Kind
#endif


-- | Set-theoretic (finite) ordinals:
--
-- > n = {0, 1, ..., n-1}
--
-- So, @Ordinal n@ has exactly n inhabitants. So especially @Ordinal 'Z@ is isomorphic to @Void@.
--
--   Since 0.5.0.0
data Ordinal (n :: nat) where
  OZ  :: Sing n -> Ordinal (Succ n)
  OS  :: Ordinal n -> Ordinal (Succ n)
  OLt :: (n :< m) ~ 'True => Sing n -> Ordinal m

-- | Since 0.2.3.0
deriving instance Typeable Ordinal

-- |  Class synonym for Peano numerals with ordinals.
--
--  Since 0.5.0.0
class (PeanoOrder kproxy, Monomorphicable (Sing :: nat -> *),
       Integral (MonomorphicRep (Sing :: nat -> *)),
       SingKind kproxy, kproxy ~ 'KProxy,
       Show (MonomorphicRep (Sing :: nat -> *))) => HasOrdinal (kproxy :: KProxy nat)
instance (PeanoOrder ('KProxy :: KProxy nat), Monomorphicable (Sing :: nat -> *),
       Integral (MonomorphicRep (Sing :: nat -> *)),
       SingKind ('KProxy :: KProxy nat),
       Show (MonomorphicRep (Sing :: nat -> *))) => HasOrdinal ('KProxy :: KProxy nat)

instance (HasOrdinal ('KProxy :: KProxy nat), SingI (n :: nat))
      => Num (Ordinal n) where
  {-# SPECIALISE instance SingI n => Num (Ordinal (n :: PN.Nat))  #-}
  {-# SPECIALISE instance SingI n => Num (Ordinal (n :: TL.Nat))  #-}
  _ + _ = error "Finite ordinal is not closed under addition."
  _ - _ = error "Ordinal subtraction is not defined"
  negate (OZ pxy) = OZ pxy
  negate _  = error "There are no negative oridnals!"
  OZ pxy * _ = OZ pxy
  _ * OZ pxy = OZ pxy
  _ * _  = error "Finite ordinal is not closed under multiplication"
  abs    = id
  signum = error "What does Ordinal sign mean?"
  fromInteger = unsafeFromInt' (Proxy :: Proxy ('KProxy :: KProxy nat)) . fromInteger

-- deriving instance Read (Ordinal n) => Read (Ordinal (Succ n))
instance (SingI n, HasOrdinal ('KProxy :: KProxy nat))
        => Show (Ordinal (n :: nat)) where
  {-# SPECIALISE instance SingI n => Show (Ordinal (n :: PN.Nat))  #-}
  {-# SPECIALISE instance SingI n => Show (Ordinal (n :: TL.Nat))  #-}
  showsPrec d o = showChar '#' . showParen True (showsPrec d (ordToInt o) . showString " / " . showsPrec d (demote $ Monomorphic (sing :: Sing n)))

instance (HasOrdinal ('KProxy :: KProxy nat))
         => Eq (Ordinal (n :: nat)) where
  {-# SPECIALISE instance Eq (Ordinal (n :: PN.Nat))  #-}
  {-# SPECIALISE instance Eq (Ordinal (n :: TL.Nat))  #-}
  o == o' = ordToInt o == ordToInt o'

instance (HasOrdinal ('KProxy :: KProxy nat)) => Ord (Ordinal (n :: nat)) where
  compare = comparing ordToInt

instance (HasOrdinal ('KProxy :: KProxy nat), SingI n)
      => Enum (Ordinal (n :: nat)) where
  fromEnum = fromIntegral . ordToInt
  toEnum   = unsafeFromInt' (Proxy :: Proxy ('KProxy :: KProxy nat)) . fromIntegral
  enumFrom = enumFromOrd
  enumFromTo = enumFromToOrd

enumFromToOrd :: forall (n :: nat).
                 (HasOrdinal ('KProxy :: KProxy nat), SingI n)
              => Ordinal n -> Ordinal n -> [Ordinal n]
enumFromToOrd ok ol =
  let k = ordToInt ok
      l = ordToInt ol
  in genericTake (l - k + 1) $ enumFromOrd ok

enumFromOrd :: forall (n :: nat).
               (HasOrdinal ('KProxy :: KProxy nat), SingI n)
            => Ordinal n -> [Ordinal n]
enumFromOrd ord = genericDrop (ordToInt ord) $ enumOrdinal (sing :: Sing n)

enumOrdinal :: (SingKind ('KProxy :: KProxy nat), PeanoOrder ('KProxy :: KProxy nat), SingI n) => Sing (n :: nat) -> [Ordinal n]
enumOrdinal (Succ n) = withSingI n $
  case lneqZero n of
    Witness ->
      OLt sZero : map succOrd (enumOrdinal n)
enumOrdinal _ = []

succOrd :: forall (n :: nat). (SingKind ('KProxy :: KProxy nat), PeanoOrder ('KProxy :: KProxy nat), SingI n) => Ordinal n -> Ordinal (Succ n)
succOrd (OLt n) =
  case succLneqSucc n (sing :: Sing n) of
    Refl -> OLt (sSucc n)
succOrd (OZ n) =
  case (succLneqSucc sZero (sSucc n), lneqZero n) of
    (Refl, Witness) -> OLt $ coerce (sym succOneCong) sOne
succOrd (OS o) =
  case (succLneqSucc sZero (sSucc (sing :: Sing n)), lneqZero (sing :: Sing n)) of
    (Refl, Witness) -> OS (OS o)

instance SingI n => Bounded (Ordinal ('PN.S n)) where
  minBound = OLt PN.SZ

  maxBound =
    case leqRefl (sing :: Sing n) of
      Witness -> sNatToOrd (sing :: Sing n)

instance (SingI m, SingI n, n ~ (m + 1)) => Bounded (Ordinal n) where
  minBound =
    case lneqZero (sing :: Sing m) of
      Witness -> OLt (sing :: Sing 0)
  {-# INLINE minBound #-}
  maxBound =
    case lneqSucc (sing :: Sing m) of
      Witness -> sNatToOrd (sing :: Sing m)
  {-# INLINE maxBound #-}


unsafeFromInt :: forall (n :: nat). (HasOrdinal ('KProxy :: KProxy nat), SingI (n :: nat))
              => MonomorphicRep (Sing :: nat -> *) -> Ordinal n
unsafeFromInt n =
    case promote (n :: MonomorphicRep (Sing :: nat -> *)) of
      Monomorphic sn ->
           case sn %:< (sing :: Sing n) of
             STrue -> sNatToOrd' (sing :: Sing n) sn
             SFalse -> error "Bound over!"

unsafeFromInt' :: forall proxy (n :: nat). (HasOrdinal ('KProxy :: KProxy nat), SingI n)
              => proxy ('KProxy :: KProxy nat) -> MonomorphicRep (Sing :: nat -> *) -> Ordinal n
unsafeFromInt' _ n =
    case promote (n :: MonomorphicRep (Sing :: nat -> *)) of
      Monomorphic sn ->
           case sn %:< (sing :: Sing n) of
             STrue -> sNatToOrd' (sing :: Sing n) sn
             SFalse -> error "Bound over!"

-- | 'sNatToOrd'' @n m@ injects @m@ as @Ordinal n@.
--
--   Since 0.5.0.0
sNatToOrd' :: (PeanoOrder ('KProxy :: KProxy nat), (m :< n) ~ 'True) => Sing (n :: nat) -> Sing m -> Ordinal n
sNatToOrd' _ m = OLt m

-- | 'sNatToOrd'' with @n@ inferred.
sNatToOrd :: (PeanoOrder ('KProxy :: KProxy nat), SingI (n :: nat), (m :< n) ~ 'True) => Sing m -> Ordinal n
sNatToOrd = sNatToOrd' sing

data CastedOrdinal n where
  CastedOrdinal :: (m :< n) ~ 'True => Sing m -> CastedOrdinal n

-- | Convert @Ordinal n@ into @Sing m@ with the proof of @'S m :<= n@.
ordToSing' :: forall (n :: nat). (PeanoOrder ('KProxy :: KProxy nat), SingI n) => Ordinal n -> CastedOrdinal n
ordToSing' (OZ sk) =
  case lneqZero sk of
    (Witness) -> CastedOrdinal sZero
ordToSing' (OS (on :: Ordinal k)) =
  withSingI (sing :: Sing n) $
  withPredSingI (Proxy :: Proxy k) (sing :: Sing n) $
    case ordToSing' on of
      CastedOrdinal m ->
        case succLneqSucc m (sing :: Sing k) of
          Refl -> CastedOrdinal (Succ m)
ordToSing' (OLt s) = CastedOrdinal s

withPredSingI :: forall proxy (n :: nat) r. PeanoOrder ('KProxy :: KProxy nat)
              => proxy (n :: nat) -> Sing (Succ n) -> (SingI n => r) -> r
withPredSingI pxy sn r = withSingI (sPred' pxy sn) r


-- | Convert @Ordinal n@ into monomorphic @Sing@
--
-- Since 0.5.0.0
ordToSing :: (PeanoOrder ('KProxy :: KProxy nat)) => Ordinal (n :: nat) -> SomeSing ('KProxy :: KProxy nat)
ordToSing (OLt n) = SomeSing n
ordToSing OZ{} = SomeSing sZero
ordToSing (OS n) =
  case ordToSing n of
    SomeSing sn ->
      case singInstance sn of
        SingInstance -> SomeSing (Succ sn)

-- | Convert ordinal into @Int@.
ordToInt :: (HasOrdinal ('KProxy :: KProxy nat), int ~ MonomorphicRep (Sing :: nat -> *))
         => Ordinal (n :: nat)
         -> int
ordToInt OZ{} = 0
ordToInt (OS n) = 1 + ordToInt n
ordToInt (OLt n) = demote $ Monomorphic n
{-# SPECIALISE ordToInt :: Ordinal (n :: PN.Nat) -> Integer #-}
{-# SPECIALISE ordToInt :: Ordinal (n :: TL.Nat) -> Integer #-}

-- | Inclusion function for ordinals.
inclusion' :: (n :< m) ~ 'True => Sing m -> Ordinal n -> Ordinal m
inclusion' _ = unsafeCoerce
{-# INLINE inclusion' #-}
{-
-- The "proof" of the correctness of the above
inclusion' :: (n :<= m) ~ 'True => Sing m -> Ordinal n -> Ordinal m
inclusion' (SS SZ) OZ = OZ
inclusion' (SS (SS _)) OZ = OZ
inclusion' (SS (SS n)) (OS m) = OS $ inclusion' (SS n) m
inclusion' _ _ = bugInGHC
-}

-- | Inclusion function for ordinals with codomain inferred.
inclusion :: ((n :<= m) ~ 'True) => Ordinal n -> Ordinal m
inclusion on = unsafeCoerce on
{-# INLINE inclusion #-}


-- | Ordinal addition.
(@+) :: forall n m. (PeanoOrder ('KProxy :: KProxy nat), SingI (n :: nat), SingI m) => Ordinal n -> Ordinal m -> Ordinal (n :+ m)
OLt s @+ n =
  case ordToSing' n of
    CastedOrdinal n' ->
      case plusStrictMonotone s (sing :: Sing n) n' (sing :: Sing m) Witness Witness of
        Witness -> OLt $ s %:+ n'
OZ {} @+ n =
  let sn = sing :: Sing n
      sm = sing :: Sing m
  in case plusLeqR sn sm of
      Witness -> inclusion n
OS (n :: Ordinal k) @+ m =
  withPredSingI n (sing :: Sing n) $
  case sing :: Sing n of
    Zero -> absurdOrd (OS n)
    Succ sn ->
      case singInstance sn of
        SingInstance ->
          let sm = sing :: Sing m
              sn' = sing :: Sing n
              sk  = sing :: Sing k
              pf = start (sSucc (sk %:+ sm))
                     === sSucc sk %:+ sm     `because` sym (plusSuccL sk sm)
                     =~= sn' %:+ sm
          in coerce pf $ OS $ n @+ m
    _ -> error "inaccessible pattern"

-- | Since @Ordinal 'Z@ is logically not inhabited, we can coerce it to any value.
--
-- Since 0.2.3.0
absurdOrd :: PeanoOrder ('KProxy :: KProxy nat) => Ordinal (Zero ('KProxy :: KProxy nat)) -> a
absurdOrd _cs = undefined -- case cs of {}

-- | 'absurdOrd' for the value in 'Functor'.
--
--   Since 0.2.3.0
vacuousOrd :: (PeanoOrder ('KProxy :: KProxy nat), Functor f) => f (Ordinal (Zero ('KProxy :: KProxy nat))) -> f a
vacuousOrd = fmap absurdOrd

-- | 'absurdOrd' for the value in 'Monad'.
--   This function will become uneccesary once 'Applicative' (and hence 'Functor')
--   become the superclass of 'Monad'.
--
--   Since 0.2.3.0
vacuousOrdM :: (PeanoOrder ('KProxy :: KProxy nat), Monad m) => m (Ordinal (Zero ('KProxy :: KProxy nat))) -> m a
vacuousOrdM = liftM absurdOrd

-- | Quasiquoter for ordinals
od :: QuasiQuoter
od = QuasiQuoter { quoteExp = foldr appE (conE 'OZ) . flip replicate (conE 'OS) . read
                 , quoteType = error "No type quoter for Ordinals"
                 , quotePat = foldr (\a b -> conP a [b]) (conP 'OZ []) . flip replicate 'OS . read
                 , quoteDec = error "No declaration quoter for Ordinals"
                 }
