{-# LANGUAGE CPP, DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, NoImplicitPrelude   #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables                 #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeFamilies          #-}
{-# LANGUAGE TypeOperators, UndecidableInstances, EmptyCase, LambdaCase #-}
-- | Type level peano natural number, some arithmetic functions and their singletons.
module Data.Type.Natural (-- * Re-exported modules.
                          module Data.Singletons,
                          -- * Natural Numbers
                          -- | Peano natural numbers. It will be promoted to the type-level natural number.
                          Nat(..),
                          SSym0, SSym1, ZSym0,
                          -- | Singleton type for 'Nat'.
                          SNat, Sing (SZ, SS),
                          -- ** Arithmetic functions and their singletons.
                          min, Min, sMin, max, Max, sMax,
                          MinSym0, MinSym1, MinSym2,
                          MaxSym0, MaxSym1, MaxSym2,
                          (:+:), (:+),
                          (:+$), (:+$$), (:+$$$),
                          (%+), (%:+), (:*), (:*:),
                          (:*$), (:*$$), (:*$$$),
                          (%:*), (%*), (:-:), (:-),
                          (:**:), (:**), (%:**), (%**),
                          (:-$), (:-$$), (:-$$$),
                          (%:-), (%-),
                          -- ** Type-level predicate & judgements
                          Leq(..), (:<=), (:<<=),
                          (:<<=$),(:<<=$$),(:<<=$$$),
                          (%:<<=), LeqInstance,
                          boolToPropLeq, boolToClassLeq, propToClassLeq,
                          LeqTrueInstance, propToBoolLeq,
                          -- * Conversion functions
                          natToInt, intToNat, sNatToInt,
                          -- * Quasi quotes for natural numbers
                          nat, snat,
                          -- * Properties of natural numbers
                          succCongEq, eqPreservesS, succCong, plusCongR, plusCongL,
                          succPlusL, plusSuccL, succPlusR, plusSuccR,
                          plusZR, plusZL, plusAssociative, plusAssoc,
                          multAssociative, multAssoc, multComm, multZL, multZR, multOneL,
                          multOneR, snEqZAbsurd, succInjective, succInj,
                          plusInjectiveL, plusInjectiveR,
                          plusMultDistr, plusMultDistrib, multPlusDistr, multPlusDistrib,
                          multCongL, multCongR,
                          sAndPlusOne, succAndPlusOneR,
                          plusComm, plusCommutative, minusCongEq, minusCongL,
                          minusNilpotent,
                          eqSuccMinus, plusMinusEqL, plusMinusEqR,
                          zAbsorbsMinR, zAbsorbsMinL, plusSR, plusNeutralR, plusNeutralL,
                          leqRhs, leqLhs, minComm, maxZL, maxComm, maxZR,
                          -- * Properties of ordering 'Leq'
                          leqRefl, leqSucc, leqTrans, plusMonotone, plusLeqL, plusLeqR,
                          minLeqL, minLeqR, leqAnitsymmetric, maxLeqL, maxLeqR,
                          leqSnZAbsurd, leqnZElim, leqSnLeq, leqPred, leqSnnAbsurd,
                          -- * Useful type synonyms and constructors
                          zero, one, two, three, four, five, six, seven, eight, nine, ten, eleven,
                          twelve, thirteen, fourteen, fifteen, sixteen, seventeen, eighteen, nineteen, twenty,
                          Zero, One, Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten,
                          Eleven, Twelve, Thirteen, Fourteen, Fifteen, Sixteen, Seventeen, Eighteen, Nineteen, Twenty,
                          ZeroSym0, OneSym0, TwoSym0, ThreeSym0, FourSym0, FiveSym0, SixSym0,
                          SevenSym0, EightSym0, NineSym0, TenSym0, ElevenSym0, TwelveSym0,
                          ThirteenSym0, FourteenSym0, FifteenSym0, SixteenSym0, SeventeenSym0,
                          EighteenSym0, NineteenSym0, TwentySym0,
                          sZero, sOne, sTwo, sThree, sFour, sFive, sSix, sSeven, sEight, sNine, sTen, sEleven,
                          sTwelve, sThirteen, sFourteen, sFifteen, sSixteen, sSeventeen, sEighteen, sNineteen, sTwenty,
                          n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20,
                          N0, N1, N2, N3, N4, N5, N6, N7, N8, N9, N10, N11, N12, N13, N14, N15, N16, N17, N18, N19, N20,

                          N0Sym0, N1Sym0, N2Sym0, N3Sym0, N4Sym0, N5Sym0, N6Sym0, N7Sym0, N8Sym0, N9Sym0, N10Sym0, N11Sym0, N12Sym0, N13Sym0, N14Sym0, N15Sym0, N16Sym0, N17Sym0, N18Sym0, N19Sym0, N20Sym0,
                          sN0, sN1, sN2, sN3, sN4, sN5, sN6, sN7, sN8, sN9, sN10, sN11, sN12, sN13, sN14,
                          sN15, sN16, sN17, sN18, sN19, sN20
                         ) where
import Data.Type.Natural.Compat
import Data.Type.Natural.Core
import Data.Type.Natural.Definitions hiding ((:<=))

import           Data.Constraint           hiding ((:-))
import           Data.Singletons
import           Data.Type.Monomorphic
import           Language.Haskell.TH
import           Language.Haskell.TH.Quote
import           Prelude                   (Bool (..), Eq (..), Int,
                                            Integral (..), Ord ((<)), error,
                                            otherwise, ($), (.))
import           Prelude                   (Ord (..))
import qualified Prelude                   as P
import           Proof.Equational

--------------------------------------------------
-- * Conversion functions.
--------------------------------------------------

-- | Convert integral numbers into 'Nat'
intToNat :: (Integral a, Ord a) => a -> Nat
intToNat 0 = Z
intToNat n
    | n < 0     = error "negative integer"
    | otherwise = S $ intToNat (n P.- 1)

-- | Convert 'Nat' into normal integers.
natToInt :: Integral n => Nat -> n
natToInt Z     = 0
natToInt (S n) = natToInt n P.+ 1

-- | Convert 'SNat n' into normal integers.
sNatToInt :: P.Num n => SNat x -> n
sNatToInt SZ     = 0
sNatToInt (SS n) = sNatToInt n P.+ 1

instance Monomorphicable (Sing :: Nat -> *) where
  type MonomorphicRep (Sing :: Nat -> *) = Int
  demote  (Monomorphic sn) = sNatToInt sn
  promote n
      | n < 0     = error "negative integer!"
      | n == 0    = Monomorphic SZ
      | otherwise = withPolymorhic (n P.- 1) $ \sn -> Monomorphic $ SS sn

--------------------------------------------------
-- * Properties
--------------------------------------------------
plusZR :: SNat n -> n :+: 'Z :=: n
plusZR SZ     = Refl
plusZR (SS n) =
 start (SS n %+ SZ)
   =~= SS (n %+ SZ)
   === SS n          `because` cong' SS (plusZR n)

plusZL :: SNat n -> 'Z :+: n :=: n
plusZL _ = Refl

succCong, succCongEq, eqPreservesS :: n :=: m -> 'S n :=: 'S m
succCong Refl = Refl
succCongEq = succCong
{-# DEPRECATED succCongEq "Will be removed in @0.5.0.0@. Use @'succCong'@ instead." #-}
eqPreservesS = succCong
{-# DEPRECATED eqPreservesS "Will be removed in @0.5.0.0@. Use @'succCong'@ instead." #-}

snEqZAbsurd :: 'S n :=: 'Z -> a
snEqZAbsurd _ = bugInGHC

succInj, succInjective :: 'S n :=: 'S m -> n :=: m
succInj Refl = Refl
succInjective = succInj
{-# DEPRECATED succInjective "Will be removed in @0.5.0.0@. \
                              Use @'succInj'@ instead." #-}

plusInjectiveL :: SNat n -> SNat m -> SNat l -> n :+ m :=: n :+ l -> m :=: l
plusInjectiveL SZ     _ _ Refl = Refl
plusInjectiveL (SS n) m l eq   = plusInjectiveL n m l $ succInjective eq

plusInjectiveR :: SNat n -> SNat m -> SNat l -> n :+ l :=: m :+ l -> n :=: m
plusInjectiveR n m l eq = plusInjectiveL l n m $
  start (l %:+ n)
    === n %:+ l   `because` plusCommutative l n
    === m %:+ l   `because` eq
    === l %:+ m   `because` plusCommutative m l

succAndPlusOneR, sAndPlusOne :: SNat n -> 'S n :=: n :+: One
succAndPlusOneR SZ = Refl
succAndPlusOneR (SS n) =
  start (SS (SS n))
    === SS (n %+ sOne) `because` cong' SS (succAndPlusOneR n)
    =~= SS n %+ sOne
sAndPlusOne = succAndPlusOneR
{-# DEPRECATED sAndPlusOne "Will be removed in @0.5.0.0@. Use @'succAndPlusOneR'@ instead." #-}

plusAssoc, plusAssociative :: SNat n -> SNat m -> SNat l
                -> n :+: (m :+: l) :=: (n :+: m) :+: l
plusAssoc SZ     _ _ = Refl
plusAssoc (SS n) m l =
  start (SS n %+ (m %+ l))
    =~= SS (n %+ (m %+ l))
    === SS ((n %+ m) %+ l)  `because` cong' SS (plusAssoc n m l)
    =~= SS (n %+ m) %+ l
    =~= (SS n %+ m) %+ l
plusAssociative = plusAssoc
{-# DEPRECATED plusAssociative "Will be removed in @0.5.0.0@. Use @'plusAssoc'@ instead." #-}

plusSR :: SNat n -> SNat m -> 'S (n :+: m) :=: n :+: 'S m
plusSR n m =
  start (SS (n %+ m))
    === (n %+ m) %+ sOne `because` succAndPlusOneR (n %+ m)
    === n %+ (m %+ sOne) `because` symmetry (plusAssoc n m sOne)
    === n %+ SS m        `because` plusCongL n (symmetry $ succAndPlusOneR m)

{-# DEPRECATED plusSR "Will be removed in @0.5.0.0@. Use @'plusSuccR'@ instead." #-}


plusCongL :: SNat n -> m :=: m' -> n :+ m :=: n :+ m'
plusCongL _ Refl = Refl

plusCongR :: SNat n -> m :=: m' -> m :+ n :=: m' :+ n
plusCongR _ Refl = Refl

plusSuccL, succPlusL :: SNat n -> SNat m -> 'S n :+ m :=: 'S (n :+ m)
plusSuccL _ _ = Refl
succPlusL = plusSuccL
{-# DEPRECATED succPlusL "Will be removed in @0.5.0.0@. Use @'plusSuccL'@ instead." #-}

plusSuccR, succPlusR :: SNat n -> SNat m -> n :+ 'S m :=: 'S (n :+ m)
plusSuccR SZ     _ = Refl
plusSuccR (SS n) m =
  start (SS n %+ SS m)
    =~= SS (n %+ SS m)
    === SS (SS (n %+ m)) `because` succCong (plusSuccR n m)
    =~= SS (SS n %+ m)

succPlusR = plusSuccR

{-# DEPRECATED succPlusR "Will be removed in @0.5.0.0@. Use @'plusSuccR'@ instead." #-}


minusCongEq, minusCongL :: n :=: m -> SNat l -> n :-: l :=: m :-: l
minusCongL Refl _ = Refl
minusCongEq = minusCongL
{-# DEPRECATED minusCongEq "Will be removed in @0.5.0.0@. Use @'minusCongL'@ instead." #-}

minusNilpotent :: SNat n -> n :-: n :=: Zero
minusNilpotent SZ = Refl
minusNilpotent (SS n) =
  start (SS n %:- SS n)
    =~= n %:- n
    === SZ     `because` minusNilpotent n


plusComm, plusCommutative :: SNat n -> SNat m -> n :+: m :=: m :+: n
plusComm SZ SZ     = Refl
plusComm SZ (SS m) =
  start (SZ %+ SS m)
    =~= SS m
    === SS (m %+ SZ) `because` cong' SS (plusCommutative SZ m)
    =~= SS m %+ SZ
plusComm (SS n) m =
  start (SS n %+ m)
    =~= SS (n %+ m)
    === SS (m %+ n)      `because` cong' SS (plusCommutative n m)
    === (m %+ n) %+ sOne `because` succAndPlusOneR (m %+ n)
    === m %+ (n %+ sOne) `because` symmetry (plusAssoc m n sOne)
    === m %+ SS n        `because` plusCongL m (symmetry $ succAndPlusOneR n)

plusCommutative = plusComm
{-# DEPRECATED plusCommutative "Will be removed in @0.5.0.0@. Use @'plusComm'@ instead." #-}

eqSuccMinus :: ((m :<<= n) ~ 'True)
            => SNat n -> SNat m -> ('S n :-: m) :=: ('S (n :-: m))
eqSuccMinus _      SZ     = Refl
eqSuccMinus (SS n) (SS m) =
  start (SS (SS n) %:- SS m)
    =~= SS n %:- m
    === SS (n %:- m)       `because` eqSuccMinus n m
    =~= SS (SS n %:- SS m)
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
eqSuccMinus _ _ = bugInGHC
#endif


plusMinusEqL :: SNat n -> SNat m -> ((n :+: m) :-: m) :=: n
plusMinusEqL SZ     m = minusNilpotent m
plusMinusEqL (SS n) m =
  case propToBoolLeq (plusLeqR n m) of
    Dict -> transitivity (eqSuccMinus (n %+ m) m) (succCong $ plusMinusEqL n m)

plusMinusEqR :: SNat n -> SNat m -> (m :+: n) :-: m :=: n
plusMinusEqR n m = transitivity (minusCongEq (plusCommutative m n) m) (plusMinusEqL n m)

zAbsorbsMinR :: SNat n -> Min n 'Z :=: 'Z
zAbsorbsMinR SZ     = Refl
zAbsorbsMinR (SS n) =
  case zAbsorbsMinR n of
    Refl -> Refl

zAbsorbsMinL :: SNat n -> Min 'Z n :=: 'Z
zAbsorbsMinL SZ     = Refl
zAbsorbsMinL (SS n) = case zAbsorbsMinL n of Refl -> Refl

minComm :: SNat n -> SNat m -> Min n m :=: Min m n
minComm SZ     SZ = Refl
minComm SZ     (SS _) = Refl
minComm (SS _) SZ = Refl
minComm (SS n) (SS m) = case minComm n m of Refl -> Refl

maxZL :: SNat n -> Max 'Z n :=: n
maxZL SZ = Refl
maxZL (SS _) = Refl

maxComm :: SNat n -> SNat m -> (Max n m) :=: (Max m n)
maxComm SZ SZ = Refl
maxComm SZ (SS _) = Refl
maxComm (SS _) SZ = Refl
maxComm (SS n) (SS m) = case maxComm n m of Refl -> Refl

maxZR :: SNat n -> Max n 'Z :=: n
maxZR n = transitivity (maxComm n SZ) (maxZL n)

multPlusDistr, multPlusDistrib :: forall n m l. SNat n -> SNat m -> SNat l -> n :* (m :+ l) :=: (n :* m) :+ (n :* l)
multPlusDistrib SZ     _ _ = Refl
multPlusDistrib (SS (n :: SNat n')) m l =
  start (SS n %* (m %+ l))
    =~= (n %* (m %+ l)) %+ (m %+ l)
    === ((n %* m) %+ (n %* l)) %+ (m %+ l)
        `because` plusCongR (m %+ l) (multPlusDistrib n m l :: n' :* (m :+ l) :=: (n' :* m) :+ (n' :* l))
    === (n %* m) %+ (n %* l) %+ (l %+ m) `because` plusCongL ((n %* m) %+ (n %* l)) (plusCommutative m l)
    === n %* m %+ (n %*l %+ (l %+ m))    `because` symmetry (plusAssoc (n %* m) (n %* l) (l %+ m))
    === n %* l %+ (l %+ m) %+ n %* m     `because` plusCommutative (n %* m) (n %*l %+ (l %+ m))
    === (n %* l %+ l) %+ m %+ n %* m     `because` plusCongR (n %* m) (plusAssoc (n %* l) l m)
    =~= (SS n %* l)   %+ m %+ n %* m
    === (SS n %* l)   %+ (m %+ (n %* m)) `because` symmetry (plusAssoc (SS n %* l) m (n %* m))
    === (SS n %* l)   %+ ((n %* m) %+ m) `because` plusCongL (SS n %* l) (plusCommutative m (n %* m))
    =~= (SS n %* l)   %+ (SS n %* m)
    === (SS n %* m)   %+ (SS n %* l)     `because` plusCommutative (SS n %* l) (SS n %* m)
multPlusDistr = multPlusDistrib
{-# DEPRECATED multPlusDistr "Will be removed in @0.5.0.0@. Use @'multPlusDistrib'@ instead." #-}

plusMultDistr, plusMultDistrib :: SNat n -> SNat m -> SNat l -> (n :+ m) :* l :=: (n :* l) :+ (m :* l)
plusMultDistrib SZ _ _ = Refl
plusMultDistrib (SS n) m l =
  start ((SS n %+ m) %* l)
    =~= SS (n %+ m) %* l
    =~= (n %+ m) %* l %+ l
    === n %* l  %+  m %* l  %+  l   `because` plusCongR l (plusMultDistrib n m l)
    === m %* l  %+  n %* l  %+  l   `because` plusCongR l (plusCommutative (n %* l) (m %* l))
    === m %* l  %+ (n %* l  %+  l)  `because` symmetry (plusAssoc (m %* l) (n %*l) l)
    =~= m %* l  %+ (SS n %* l)
    === (SS n %* l)  %+  (m %* l)   `because` plusCommutative (m %* l) (SS n %* l)

plusMultDistr = plusMultDistrib
{-# DEPRECATED plusMultDistr "Will be removed in @0.5.0.0@. Use @'plusMultDistrib'@ instead." #-}

multAssoc, multAssociative :: SNat n -> SNat m -> SNat l -> n :* (m :* l) :=: (n :* m) :* l
multAssoc SZ     _ _ = Refl
multAssoc (SS n) m l =
  start (SS n %* (m %* l))
    =~= n %* (m %* l) %+ (m %* l)
    === (n %* m) %* l %+ (m %* l) `because` plusCongR (m %* l) (multAssoc n m l)
    === (n %* m %+ m) %* l        `because` symmetry (plusMultDistrib (n %* m) m l)
    =~= (SS n %* m) %* l
multAssociative = multAssoc
{-# DEPRECATED multAssociative "Will be removed in @0.5.0.0@. Use @'multAssoc'@ instead." #-}
multZL :: SNat m -> Zero :* m :=: Zero
multZL _ = Refl

multZR :: SNat m -> m :* Zero :=: Zero
multZR SZ = Refl
multZR (SS n) =
  start (SS n %* SZ)
    =~= n %* SZ %+ SZ
    === SZ %+ SZ      `because` plusCongR SZ (multZR n)
    =~= SZ

multOneL :: SNat n -> One :* n :=: n
multOneL n =
  start (sOne %* n)
    =~= sZero %* n %+ n
    =~= sZero %:+ n
    =~= n

multOneR :: SNat n -> n :* One :=: n
multOneR SZ = Refl
multOneR (SS n) =
  start (SS n %* sOne)
    =~= n %* sOne %+ sOne
    === n %+ sOne         `because` plusCongR sOne (multOneR n)
    === SS n              `because` symmetry (succAndPlusOneR n)

multCongL :: SNat n -> m :=: l -> n :* m :=: n :* l
multCongL _ Refl = Refl

multCongR :: SNat n -> m :=: l -> m :* n :=: l :* n
multCongR _ Refl = Refl

multComm :: SNat n -> SNat m -> n :* m :=: m :* n
multComm SZ m =
  start (SZ %* m)
    =~= SZ
    === m %* SZ `because` symmetry (multZR m)
multComm (SS n) m =
  start (SS n %* m)
    =~= n %* m %+ m
    === m %* n %+ m          `because` plusCongR m (multComm n m)
    === m %* n %+ m %* sOne  `because` plusCongL (m %* n) (symmetry $ multOneR m)
    === m %* (n %+ sOne)     `because` symmetry (multPlusDistrib m n sOne)
    === m %* SS n            `because` multCongL m (symmetry $ succAndPlusOneR n)

plusNeutralR :: SNat n -> SNat m -> n :+ m :=: n -> m :=: 'Z
plusNeutralR SZ m eq =
  start m
    =~= SZ %:+ m
    === SZ       `because` eq
plusNeutralR (SS n) m eq = plusNeutralR n m $ succInjective eq

plusNeutralL :: SNat n -> SNat m -> n :+ m :=: m -> n :=: 'Z
plusNeutralL n m eq = plusNeutralR m n $
  start (m %:+ n)
    === n %:+ m   `because` plusCommutative m n
    === m         `because` eq

--------------------------------------------------
-- * Properties of 'Leq'
--------------------------------------------------

leqRefl :: SNat n -> Leq n n
leqRefl SZ = ZeroLeq SZ
leqRefl (SS n) = SuccLeqSucc $ leqRefl n

leqSucc :: SNat n -> Leq n ('S n)
leqSucc SZ = ZeroLeq sOne
leqSucc (SS n) = SuccLeqSucc $ leqSucc n

leqTrans :: Leq n m -> Leq m l -> Leq n l
leqTrans (ZeroLeq _) leq = ZeroLeq $ leqRhs leq
leqTrans (SuccLeqSucc nLeqm) (SuccLeqSucc mLeql) = SuccLeqSucc $ leqTrans nLeqm mLeql
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
leqTrans _ _ = error "impossible!"
#endif

instance Preorder Leq where
  reflexivity = leqRefl
  transitivity = leqTrans

plusMonotone :: Leq n m -> Leq l k -> Leq (n :+: l) (m :+: k)
plusMonotone (ZeroLeq m) (ZeroLeq k) = ZeroLeq (m %+ k)
plusMonotone (ZeroLeq m) (SuccLeqSucc leq) =
  case sym $ plusSuccR m (leqRhs leq) of
    Refl -> SuccLeqSucc $ plusMonotone (ZeroLeq m) leq
plusMonotone (SuccLeqSucc leq) leq' = SuccLeqSucc $ plusMonotone leq leq'

plusLeqL :: SNat n -> SNat m -> Leq n (n :+: m)
plusLeqL SZ     m = ZeroLeq $ coerce (symmetry $ plusZL m) m
plusLeqL (SS n) m =
  start (SS n)
    =<= SS (n %+ m) `because` SuccLeqSucc (plusLeqL n m)
    =~= SS n %+ m

plusLeqR :: SNat n -> SNat m -> Leq m (n :+: m)
plusLeqR n m =
  case plusCommutative n m of
    Refl -> plusLeqL m n

minLeqL :: SNat n -> SNat m -> Leq (Min n m) n
minLeqL SZ m = case zAbsorbsMinL m of Refl -> ZeroLeq SZ
minLeqL n SZ = case zAbsorbsMinR n of Refl -> ZeroLeq n
minLeqL (SS n) (SS m) = SuccLeqSucc (minLeqL n m)

minLeqR :: SNat n -> SNat m -> Leq (Min n m) m
minLeqR n m = case minComm n m of Refl -> minLeqL m n

leqAnitsymmetric :: Leq n m -> Leq m n -> n :=: m
leqAnitsymmetric (ZeroLeq _) (ZeroLeq _) = Refl
leqAnitsymmetric (SuccLeqSucc leq1) (SuccLeqSucc leq2) = succCong $ leqAnitsymmetric leq1 leq2
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
leqAnitsymmetric _ _ = error "impossible!"
#endif

maxLeqL :: SNat n -> SNat m -> Leq n (Max n m)
maxLeqL SZ m = ZeroLeq (sMax SZ m)
maxLeqL n SZ = case maxZR n of
                 Refl -> leqRefl n
maxLeqL (SS n) (SS m) = SuccLeqSucc $ maxLeqL n m

maxLeqR :: SNat n -> SNat m -> Leq m (Max n m)
maxLeqR n m = case maxComm n m of
                Refl -> maxLeqL m n

leqSnZAbsurd :: Leq ('S n) 'Z -> a
leqSnZAbsurd = \case {}

leqnZElim :: Leq n 'Z -> n :=: 'Z
leqnZElim (ZeroLeq SZ) = Refl

leqSnLeq :: Leq ('S n) m -> Leq n m
leqSnLeq (SuccLeqSucc leq) =
  let n = leqLhs leq
      m = SS $ leqRhs leq
  in start n
       =<= SS n   `because` leqSucc n
       =<= m      `because` SuccLeqSucc leq
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
leqSnLeq _ = bugInGHC
#endif

leqPred :: Leq ('S n) ('S m) -> Leq n m
leqPred (SuccLeqSucc leq) = leq
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
leqPred _ = bugInGHC
#endif

leqSnnAbsurd :: Leq ('S n) n -> a
leqSnnAbsurd (SuccLeqSucc leq) =
  case leqLhs leq of
    SS _ -> leqSnnAbsurd leq
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
    _    -> bugInGHC "cannot be occured"
leqSnnAbsurd _ = bugInGHC
#endif

--------------------------------------------------
-- * Quasi Quoter
--------------------------------------------------

-- | Quotesi-quoter for 'Nat'. This can be used for an expression, pattern and type.
--
--   for example: @sing :: SNat ([nat| 2 |] :+ [nat| 5 |])@
nat :: QuasiQuoter
nat = QuasiQuoter { quoteExp = P.foldr appE (conE 'Z) . P.flip P.replicate (conE 'S) . P.read
                  , quotePat = P.foldr (\a b -> conP a [b]) (conP 'Z []) . P.flip P.replicate 'S . P.read
                  , quoteType = P.foldr appT (conT 'Z) . P.flip P.replicate (conT 'S) . P.read
                  , quoteDec = error "not implemented"
                  }

-- | Quotesi-quoter for 'SNat'. This can be used for an expression, pattern and type.
--
--  For example: @[snat|12|] '%+' [snat| 5 |]@, @'sing' :: [snat| 12 |]@, @f [snat| 12 |] = \"hey\"@
snat :: QuasiQuoter
snat = QuasiQuoter { quoteExp = P.foldr appE (conE 'SZ) . P.flip P.replicate (conE 'SS) . P.read
                   , quotePat = P.foldr (\a b -> conP a [b]) (conP 'SZ []) . P.flip P.replicate 'SS . P.read
                   , quoteType = appT (conT ''SNat) . P.foldr appT (conT 'Z) . P.flip P.replicate (conT 'S) . P.read
                   , quoteDec = error "not implemented"
                   }
