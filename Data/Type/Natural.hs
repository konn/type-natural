{-# LANGUAGE CPP, DataKinds, EmptyCase, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, KindSignatures, LambdaCase, MultiParamTypeClasses       #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables                     #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeFamilies, TypeInType  #-}
{-# LANGUAGE TypeOperators, UndecidableInstances                            #-}
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
                          IsPeano(..),
                          succCongEq, plusCongR, plusCongL, succPlusL, succPlusR,
                          eqPreservesS, plusAssociative,
                          multAssociative, snEqZAbsurd, succInjective, plusInjectiveL, plusInjectiveR,
                          plusMultDistr, multPlusDistr, multCongL, multCongR, multCongEq,
                          sAndPlusOne, plusCommutative, minusCongEq,
                          plusMinusEqL, plusMinusEqR, leqRhs, leqLhs,
                          plusSR, plusNeutralR, plusNeutralL,
                          -- eqSuccMinus, zAbsorbsMinR, zAbsorbsMinL,
                          -- minComm, maxZeroL, maxComm, maxZeroR, plusLeqL, plusLeqR,
                          -- minLeqL, minLeqR, leqAnitsymmetric, maxLeqL, maxLeqR,
                          -- leqSnZAbsurd, leqnZElim, leqSnLeq, leqPred, leqSnnAbsurd,
                          -- * Properties of ordering 'Leq'
                          leqRefl, leqSucc, leqTrans, plusMonotone, 
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
                         )
       where
import Data.Type.Natural.Class hiding (One, Zero)
import Data.Type.Natural.Core
import Data.Type.Natural.Definitions hiding ((:<=))

import Data.Kind
import Data.Singletons
import Data.Type.Monomorphic
import Proof.Equational
import Proof.Propositional
import Data.Void
import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Quote

--------------------------------------------------
-- * Conversion functions.
--------------------------------------------------

-- | Convert integral numbers into 'Nat'
intToNat :: (Integral a, Ord a) => a -> Nat
intToNat 0 = Z
intToNat n
    | n < 0     = error "negative integer"
    | otherwise = S $ intToNat (n - 1)

-- | Convert 'Nat' into normal integers.
natToInt :: Integral n => Nat -> n
natToInt Z     = 0
natToInt (S n) = natToInt n + 1

-- | Convert 'SNat n' into normal integers.
sNatToInt :: Num n => SNat x -> n
sNatToInt SZ     = 0
sNatToInt (SS n) = sNatToInt n + 1

instance Monomorphicable (Sing :: Nat -> Type) where
  type MonomorphicRep (Sing :: Nat -> Type) = Int
  demote  (Monomorphic sn) = sNatToInt sn
  promote n
      | n < 0     = error "negative integer!"
      | n == 0    = Monomorphic SZ
      | otherwise = withPolymorhic (n - 1) $ \sn -> Monomorphic $ SS sn

--------------------------------------------------
-- * Properties
--------------------------------------------------

-- | Since 0.5.0.0
instance IsPeano Nat where
  induction base _step SZ = base
  induction base step (SS n) = step n (induction base step n)

  plusMinus n SZ =
    start (n %:+ SZ %:- SZ)
      === (n %:- SZ)        `because` minusCongL (plusZeroR n) SZ 
      =~= n
  plusMinus n (SS m) =
    start (n %:+ SS m %:- SS m)
      === SS (n %:+ m) %:- SS m `because` minusCongL (plusSuccR n m) (SS m)
      =~= (n %:+ m) %:- m
      === n                     `because` plusMinus n m

  succInj Refl = Refl
  succOneCong = Refl
  succNonCyclic _ a = case a of {}

  plusZeroL _   = Refl  
  plusSuccL _ _ = Refl

  multZeroL _   = Refl
  multSuccL _ _ = Refl

  predSucc _ = Refl

snEqZAbsurd :: SingI n => 'S n :=: 'Z -> a
snEqZAbsurd = absurd . succNonCyclic sing

{-# DEPRECATED plusCommutative "use @'plusComm'@ instead." #-}
plusCommutative :: (IsPeano nat) => Sing (n :: nat) -> Sing m -> n :+ m :~: m :+ n
plusCommutative = plusComm

plusInjectiveL :: SNat n -> SNat m -> SNat l -> n :+ m :=: n :+ l -> m :=: l
plusInjectiveL SZ     _ _ Refl = Refl
plusInjectiveL (SS n) m l eq   = plusInjectiveL n m l $ succInj eq

plusInjectiveR :: SNat n -> SNat m -> SNat l -> n :+ l :=: m :+ l -> n :=: m
plusInjectiveR n m l eq = plusInjectiveL l n m $
  start (l %:+ n)
    === n %:+ l   `because` plusComm l n
    === m %:+ l   `because` eq
    === l %:+ m   `because` plusComm m l

{-# DEPRECATED sAndPlusOne "Use @'succAndPlusOneR'@" #-}
sAndPlusOne :: SNat n -> 'S n :=: n :+: One
sAndPlusOne = succAndPlusOneR

{-# DEPRECATED plusAssociative "Use @'plusAssoc'@ instead." #-}
plusAssociative :: SNat n -> SNat m -> SNat l
                -> n :+: (m :+: l) :=: (n :+: m) :+: l
plusAssociative n m l = sym $ plusAssoc n m l

{-# DEPRECATED plusSR "Use @'plusSuccR'@ instead." #-}
plusSR :: SNat n -> SNat m -> 'S (n :+: m) :=: n :+: 'S m
plusSR n m = sym $ plusSuccR n m

succPlusR :: SNat n -> SNat m -> n :+ 'S m :=: 'S (n :+ m)
succPlusR = plusSuccR
{-# DEPRECATED succPlusR "Use @'plusSuccR'@ instead." #-}

succInjective :: S (n :: Nat) :~: S m -> n :~: m
succInjective = succInj
{-# DEPRECATED succInjective "Use @'succInj'@ instead." #-}

-- eqSuccMinus :: ((m :<<= n) ~ 'True)
--             => SNat n -> SNat m -> ('S n :-: m) :=: ('S (n :-: m))
-- eqSuccMinus _      SZ     = Refl
-- eqSuccMinus (SS n) (SS m) =
--   start (SS (SS n) %:- SS m)
--     =~= SS n %:- m
--     === SS (n %:- m)       `because` eqSuccMinus n m
--     =~= SS (SS n %:- SS m)
-- #if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
-- eqSuccMinus _ _ = bugInGHC
-- #endif

instance PeanoOrder Nat where
  leqZero _ = Witness
  leqSucc _      _      Witness = Witness
  viewLeq SZ     n      Witness = LeqZero n
  viewLeq (SS n) (SS m) Witness = LeqSucc n m Witness
  viewLeq (SS _) SZ     a       = case a of {}

  minLeqL SZ SZ     = Witness
  minLeqL SZ (SS _) = Witness
  minLeqL (SS _) SZ = Witness
  minLeqL (SS n) (SS m) = minLeqL n m

  minLeqR SZ SZ     = Witness
  minLeqR SZ (SS _) = Witness
  minLeqR (SS _) SZ = Witness
  minLeqR (SS n) (SS m) = minLeqR n m

  minLargest SZ     _      _  _ _       = Witness
  minLargest (SS _) SZ SZ     _ a       = case a of {}
  minLargest (SS _) SZ (SS _) a Witness = case a of {}
  minLargest (SS _) (SS _) SZ _ a       = case a of {}
  minLargest (SS n) (SS m) (SS l) Witness Witness =
    minLargest n m l Witness Witness

  maxLeqL SZ      SZ     = Witness
  maxLeqL SZ      (SS _) = Witness
  maxLeqL (SS n)  SZ     = leqRefl n
  maxLeqL (SS n)  (SS m) = maxLeqL n m

  maxLeqR SZ SZ         = Witness
  maxLeqR (SS _) SZ     = Witness
  maxLeqR (SS n) (SS m) = maxLeqR n m
  maxLeqR SZ     (SS m) = leqRefl m

  maxLeast SZ     SZ     SZ      Witness _ = Witness
  maxLeast SZ     SZ     (SS _)  a _       = case a of {}
  maxLeast SZ     (SS _) SZ      a _       = case a of {}
  maxLeast SZ     (SS _) (SS _)  a _       = case a of {}
  maxLeast (SS _) _      _       _ a       = case a of {}

plusMinusEqL :: SNat n -> SNat m -> ((n :+: m) :-: m) :=: n
plusMinusEqL = plusMinus

{-# DEPRECATED minusCongEq "Use @'minusCongL'@ instead." #-}
minusCongEq :: n :~: m -> Sing l -> n :- l :~: m :- l
minusCongEq = minusCongL

{-# DEPRECATED plusMinusEqR "Prove on your own." #-}
plusMinusEqR :: SNat n -> SNat m -> (m :+: n) :-: m :=: n
plusMinusEqR n m = transitivity (minusCongEq (plusCommutative m n) m) (plusMinusEqL n m)

-- zAbsorbsMinR :: SNat n -> Min n 'Z :=: 'Z
-- zAbsorbsMinR SZ     = Refl
-- zAbsorbsMinR (SS n) =
--   case zAbsorbsMinR n of
--     Refl -> Refl

-- zAbsorbsMinL :: SNat n -> Min 'Z n :=: 'Z
-- zAbsorbsMinL SZ     = Refl
-- zAbsorbsMinL (SS n) = case zAbsorbsMinL n of Refl -> Refl

-- minComm :: SNat n -> SNat m -> Min n m :=: Min m n
-- minComm SZ     SZ = Refl
-- minComm SZ     (SS _) = Refl
-- minComm (SS _) SZ = Refl
-- minComm (SS n) (SS m) = case minComm n m of Refl -> Refl

-- maxZeroL :: SNat n -> Max 'Z n :=: n
-- maxZeroL SZ = Refl
-- maxZeroL (SS _) = Refl

-- maxComm :: SNat n -> SNat m -> (Max n m) :=: (Max m n)
-- maxComm SZ SZ = Refl
-- maxComm SZ (SS _) = Refl
-- maxComm (SS _) SZ = Refl
-- maxComm (SS n) (SS m) = case maxComm n m of Refl -> Refl

-- maxZeroR :: SNat n -> Max n 'Z :=: n
-- maxZeroR n = transitivity (maxComm n SZ) (maxZeroL n)

{-# DEPRECATED multPlusDistr "Use @'multPlusDistirb'@ instead." #-}
multPlusDistr :: SNat n -> SNat m -> SNat l -> n :* (m :+ l) :=: (n :* m) :+ (n :* l)
multPlusDistr = multPlusDistrib

{-# DEPRECATED plusMultDistr "Use @'plusMultDistirb'@ instead." #-}
plusMultDistr :: SNat n -> SNat m -> SNat l -> (n :+ m) :* l :=: (n :* l) :+ (m :* l)
plusMultDistr = plusMultDistrib

{-# DEPRECATED multAssociative "Use @'multAssoc'@ instead." #-}
multAssociative :: SNat n -> SNat m -> SNat l -> n :* (m :* l) :=: (n :* m) :* l
multAssociative n m l = sym $ multAssoc n m l

{-# DEPRECATED eqPreservesS "Use @'succCong'@ instead." #-}
eqPreservesS :: n :~: m -> S n :~: S m
eqPreservesS = succCong

plusNeutralR :: SNat n -> SNat m -> n :+ m :=: n -> m :=: 'Z
plusNeutralR n m npmn = plusEqCancelL n m SZ (npmn `trans` sym (plusZeroR n))

plusNeutralL :: SNat n -> SNat m -> n :+ m :=: m -> n :=: 'Z
plusNeutralL n m npmm = plusNeutralR m n (plusComm m n `trans` npmm)

-- --------------------------------------------------
-- -- * Properties of 'Leq'
-- --------------------------------------------------

-- leqRefl :: SNat n -> Leq n n
-- leqRefl SZ = ZeroLeq SZ
-- leqRefl (SS n) = SuccLeqSucc $ leqRefl n

-- leqSucc :: SNat n -> Leq n ('S n)
-- leqSucc SZ = ZeroLeq sOne
-- leqSucc (SS n) = SuccLeqSucc $ leqSucc n

-- leqTrans :: Leq n m -> Leq m l -> Leq n l
-- leqTrans (ZeroLeq _) leq = ZeroLeq $ leqRhs leq
-- leqTrans (SuccLeqSucc nLeqm) (SuccLeqSucc mLeql) = SuccLeqSucc $ leqTrans nLeqm mLeql
-- #if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
-- leqTrans _ _ = error "impossible!"
-- #endif

-- instance Preorder Leq where
--   reflexivity = leqRefl
--   transitivity = leqTrans

-- plusMonotone :: Leq n m -> Leq l k -> Leq (n :+: l) (m :+: k)
-- plusMonotone (ZeroLeq m) (ZeroLeq k) = ZeroLeq (m %+ k)
-- plusMonotone (ZeroLeq m) (SuccLeqSucc leq) =
--   case plusSR m (leqRhs leq) of
--     Refl -> SuccLeqSucc $ plusMonotone (ZeroLeq m) leq
-- plusMonotone (SuccLeqSucc leq) leq' = SuccLeqSucc $ plusMonotone leq leq'

-- plusLeqL :: SNat n -> SNat m -> Leq n (n :+: m)
-- plusLeqL SZ     m = ZeroLeq $ coerce (symmetry $ plusZeroL m) m
-- plusLeqL (SS n) m =
--   start (SS n)
--     =<= SS (n %+ m) `because` SuccLeqSucc (plusLeqL n m)
--     =~= SS n %+ m

-- plusLeqR :: SNat n -> SNat m -> Leq m (n :+: m)
-- plusLeqR n m =
--   case plusCommutative n m of
--     Refl -> plusLeqL m n

-- minLeqL :: SNat n -> SNat m -> Leq (Min n m) n
-- minLeqL SZ m = case zAbsorbsMinL m of Refl -> ZeroLeq SZ
-- minLeqL n SZ = case zAbsorbsMinR n of Refl -> ZeroLeq n
-- minLeqL (SS n) (SS m) = SuccLeqSucc (minLeqL n m)

-- minLeqR :: SNat n -> SNat m -> Leq (Min n m) m
-- minLeqR n m = case minComm n m of Refl -> minLeqL m n

-- leqAnitsymmetric :: Leq n m -> Leq m n -> n :=: m
-- leqAnitsymmetric (ZeroLeq _) (ZeroLeq _) = Refl
-- leqAnitsymmetric (SuccLeqSucc leq1) (SuccLeqSucc leq2) = eqPreserveSS $ leqAnitsymmetric leq1 leq2
-- #if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
-- leqAnitsymmetric _ _ = error "impossible!"
-- #endif

-- maxLeqL :: SNat n -> SNat m -> Leq n (Max n m)
-- maxLeqL SZ m = ZeroLeq (sMax SZ m)
-- maxLeqL n SZ = case maxZeroR n of
--                  Refl -> leqRefl n
-- maxLeqL (SS n) (SS m) = SuccLeqSucc $ maxLeqL n m

-- maxLeqR :: SNat n -> SNat m -> Leq m (Max n m)
-- maxLeqR n m = case maxComm n m of
--                 Refl -> maxLeqL m n

-- leqSnZAbsurd :: Leq ('S n) 'Z -> a
-- leqSnZAbsurd = \case {}

-- leqnZElim :: Leq n 'Z -> n :=: 'Z
-- leqnZElim (ZeroLeq SZ) = Refl

-- leqSnLeq :: Leq ('S n) m -> Leq n m
-- leqSnLeq (SuccLeqSucc leq) =
--   let n = leqLhs leq
--       m = SS $ leqRhs leq
--   in start n
--        =<= SS n   `because` leqSucc n
--        =<= m      `because` SuccLeqSucc leq
-- #if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
-- leqSnLeq _ = bugInGHC
-- #endif

-- leqPred :: Leq ('S n) ('S m) -> Leq n m
-- leqPred (SuccLeqSucc leq) = leq
-- #if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
-- leqPred _ = bugInGHC
-- #endif

-- leqSnnAbsurd :: Leq ('S n) n -> a
-- leqSnnAbsurd (SuccLeqSucc leq) =
--   case leqLhs leq of
--     SS _ -> leqSnnAbsurd leq
-- #if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
--     _    -> bugInGHC "cannot be occured"
-- leqSnnAbsurd _ = bugInGHC
-- #endif

{-# DEPRECATED succCongEq "Use @'succCong'@ instead." #-}
succCongEq :: n :~: m -> S n :~: S m
succCongEq = succCong

{-# DEPRECATED succPlusL "Use @'plusSuccL'@ instead." #-}
succPlusL :: SNat n -> SNat m -> (S n :+ m) :~: S (n :+ m)
succPlusL = plusSuccL

{-# DEPRECATED multCongEq "Use @'multCong'@ instead." #-}
multCongEq :: n :~: m -> l :~: k -> n :* l :~: m :* (k :: nat)
multCongEq = multCong

--------------------------------------------------
-- * Quasi Quoter
--------------------------------------------------

-- | Quotesi-quoter for 'Nat'. This can be used for an expression, pattern and type.
--
--   for example: @sing :: SNat ([nat| 2 |] :+ [nat| 5 |])@
nat :: QuasiQuoter
nat = QuasiQuoter { quoteExp = foldr appE (conE 'Z) . flip replicate (conE 'S) . read
                  , quotePat = foldr (\a b -> conP a [b]) (conP 'Z []) . flip replicate 'S . read
                  , quoteType = foldr appT (conT 'Z) . flip replicate (conT 'S) . read
                  , quoteDec = error "not implemented"
                  }

-- | Quotesi-quoter for 'SNat'. This can be used for an expression, pattern and type.
--
--  For example: @[snat|12|] '%+' [snat| 5 |]@, @'sing' :: [snat| 12 |]@, @f [snat| 12 |] = \"hey\"@
snat :: QuasiQuoter
snat = QuasiQuoter { quoteExp = foldr appE (conE 'SZ) . flip replicate (conE 'SS) . read
                   , quotePat = foldr (\a b -> conP a [b]) (conP 'SZ []) . flip replicate 'SS . read
                   , quoteType = appT (conT ''SNat) . foldr appT (conT 'Z) . flip replicate (conT 'S) . read
                   , quoteDec = error "not implemented"
                   }
