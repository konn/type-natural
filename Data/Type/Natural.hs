{-# LANGUAGE CPP, DataKinds, EmptyCase, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, KindSignatures, LambdaCase, MultiParamTypeClasses       #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables                     #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeFamilies              #-}
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
                          Leq(..), (:<=), LeqInstance,
                          boolToPropLeq, boolToClassLeq, propToClassLeq,
                          propToBoolLeq,
                          -- * Conversion functions
                          natToInt, intToNat, sNatToInt,
                          -- * Quasi quotes for natural numbers
                          snat,
                          -- * Properties of natural numbers
                          IsPeano(..),
                          plusCong, plusCongR, plusCongL,
                          snEqZAbsurd, plusInjectiveL, plusInjectiveR,
                          multCongL, multCongR, multCong,
                          plusMinusEqL,
                          plusNeutralR, plusNeutralL,
                          -- * Properties of ordering 'Leq'
                          PeanoOrder(..),
                          reflToSEqual, sLeqReflexive, nonSLeqToLT,
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
import Data.Type.Natural.Class hiding (One, Zero, sOne, sZero)
import Data.Type.Natural.Core
import Data.Type.Natural.Definitions hiding ((:<=))
import Data.Singletons
import Data.Singletons.Prelude.Ord
import Data.Singletons.Decide
import Data.Type.Monomorphic
import Proof.Equational
import Proof.Propositional hiding (Not)
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

instance Monomorphicable (Sing :: Nat -> *) where
  type MonomorphicRep (Sing :: Nat -> *) = Integer
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
  {-# SPECIALISE instance IsPeano Nat #-}
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

snEqZAbsurd :: SingI n => 'S n :~: 'Z -> a
snEqZAbsurd = absurd . succNonCyclic sing

plusInjectiveL :: SNat n -> SNat m -> SNat l -> n :+ m :~: n :+ l -> m :~: l
plusInjectiveL SZ     _ _ Refl = Refl
plusInjectiveL (SS n) m l eq   = plusInjectiveL n m l $ succInj eq

plusInjectiveR :: SNat n -> SNat m -> SNat l -> n :+ l :~: m :+ l -> n :~: m
plusInjectiveR n m l eq = plusInjectiveL l n m $
  start (l %:+ n)
    === n %:+ l   `because` plusComm l n
    === m %:+ l   `because` eq
    === l %:+ m   `because` plusComm m l

reflToSEqual :: SNat n -> SNat m -> n :~: m -> IsTrue (n :== m)
reflToSEqual SZ     _      Refl = Witness
reflToSEqual (SS n) (SS m) Refl = reflToSEqual n m Refl
reflToSEqual (SS _) SZ refl = case refl of {}

sequalToRefl :: SNat n -> SNat m -> IsTrue (n :== m) -> n :~: m
sequalToRefl SZ     SZ     Witness = Refl
sequalToRefl SZ     (SS _) witness = case witness of {}
sequalToRefl (SS n) (SS m) Witness = succCong $ sequalToRefl n m Witness
sequalToRefl (SS _) SZ     witness = case witness of {}

snequalToNoRefl :: SNat n -> SNat m -> IsTrue (Not (n :== m)) -> n :~: m -> Void
snequalToNoRefl SZ     _ Witness = \case  {}
snequalToNoRefl (SS _) _ Witness = \case  {}

sequalSym :: SNat n -> SNat m -> (n :== m) :~: (m :== n)
sequalSym SZ SZ         = Refl
sequalSym SZ (SS _)     = Refl
sequalSym (SS _) SZ     = Refl
sequalSym (SS n) (SS m) = sequalSym n m

sleqFlip :: SNat n -> SNat m -> (n :~: m -> Void) -> (m :<= n) :~: Not (n :<= m)
sleqFlip SZ     SZ     neq = absurd $ neq Refl
sleqFlip SZ     (SS _) _   = Refl
sleqFlip (SS _) SZ     _   = Refl
sleqFlip (SS n) (SS m) neq = sleqFlip n m (neq . succCong)

sLeqReflexive :: SNat n -> SNat m -> IsTrue (n :== m) -> IsTrue (n :<= m)
sLeqReflexive SZ     _      Witness = Witness
sLeqReflexive (SS n) (SS m) Witness = sLeqReflexive n m Witness
sLeqReflexive (SS _) SZ  witness = case witness of {}

nonSLeqToLT :: (n :<= m) ~ 'False => SNat n -> SNat m -> Compare m n :~: 'LT
nonSLeqToLT n m = withRefl (sequalSym n m) $
  case m %:== n of
    STrue -> case sLeqReflexive n m Witness of {}
    SFalse ->
      case m %:<= n of
        STrue  -> Refl
        SFalse -> case sleqFlip n m $ snequalToNoRefl n m Witness of {}

instance PeanoOrder Nat where
  {-# SPECIALISE instance PeanoOrder Nat #-}
  leqZero _ = Witness
  leqSucc _      _      Witness = Witness
  viewLeq SZ     n      Witness = LeqZero n
  viewLeq (SS n) (SS m) Witness = LeqSucc n m Witness
  viewLeq (SS _) SZ     a       = case a of {}

  ltToLeq n m Refl =
    case n %:== m of
      SFalse -> case n %:<= m of
        STrue -> Witness
  eqlCmpEQ n m Refl =
    case n %:== m of
      STrue  -> Refl
      SFalse -> absurd $ snequalToNoRefl n m Witness Refl

  eqToRefl n m Refl =
    case n %:== m of
      STrue -> sequalToRefl n m Witness
      SFalse -> case n %:<= m of {}

  leqToCmp n m Witness =
    case n %:== m of
      STrue  -> Left $ sequalToRefl n m Witness
      SFalse -> Right Refl

  flipCompare n m =
    case n %:== m of
      STrue -> withRefl (sequalSym n m) Refl
      SFalse -> withRefl (sequalSym n m) $
        case n %:<= m of
          STrue -> withRefl (sleqFlip n m (snequalToNoRefl n m Witness)) $
            case m %:<= n of
              SFalse -> Refl
          SFalse -> withRefl (sleqFlip n m (snequalToNoRefl n m Witness)) $
            case m %:<= n of
              STrue -> Refl

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

  leqReversed _ _ = Refl
  lneqReversed _ _ = Refl
  lneqSuccLeq _ _ = Refl

plusMinusEqL :: SNat n -> SNat m -> ((n :+: m) :-: m) :~: n
plusMinusEqL = plusMinus

plusNeutralR :: SNat n -> SNat m -> n :+ m :~: n -> m :~: 'Z
plusNeutralR n m npmn = plusEqCancelL n m SZ (npmn `trans` sym (plusZeroR n))

plusNeutralL :: SNat n -> SNat m -> n :+ m :~: m -> n :~: 'Z
plusNeutralL n m npmm = plusNeutralR m n (plusComm m n `trans` npmm)

--------------------------------------------------
-- * Quasi Quoter
--------------------------------------------------

-- | Quotesi-quoter for 'SNat'. This can be used for an expression.
--
--  For example: @[snat|12|] '%:+' [snat| 5 |]@.
snat :: QuasiQuoter
snat = mkSNatQQ [t| Nat |]

