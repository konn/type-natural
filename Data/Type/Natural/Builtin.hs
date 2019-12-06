{-# LANGUAGE CPP, ConstraintKinds, DataKinds, EmptyCase, ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts, GADTs, InstanceSigs, PolyKinds, RankNTypes   #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators                   #-}
{-# LANGUAGE UndecidableInstances                                           #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Coercion between Peano Numerals @'Data.Type.Natural.Nat'@ and builtin naturals @'GHC.TypeLits.Nat'@
module Data.Type.Natural.Builtin
       ( -- * Sysnonym to avoid confusion
         Peano,
         -- * Coercion between builtin type-level natural and peano numerals
         FromPeano, ToPeano, sFromPeano, sToPeano, leqqAndLeq,
         -- * Properties of @'FromPeano'@ and @'ToPeano'@.
         fromPeanoInjective, toPeanoInjective,
         -- ** Bijection
         fromToPeano, toFromPeano,
         -- ** Algebraic isomorphisms
         fromPeanoZeroCong, toPeanoZeroCong,
         fromPeanoOneCong,  toPeanoOneCong,
         fromPeanoSuccCong, toPeanoSuccCong,
         fromPeanoPlusCong, toPeanoPlusCong,
         fromPeanoMultCong, toPeanoMultCong,
         fromPeanoMonotone, toPeanoMonotone,
         -- * Peano and commutative ring axioms for built-in @'GHC.TypeLits.Nat'@
         IsPeano(..),
         inductionNat,
         -- * QuasiQuotes
         snat,
         -- * Re-exports
         module Data.Type.Natural.Singleton.Compat
       )
       where
import Data.Type.Natural.Singleton.Compat
import Data.Type.Natural.Class

import           Data.Singletons.Decide       (SDecide (..))
import           Data.Singletons.Decide       (Decision (..))
import           Data.Singletons.Prelude      (Sing (..), SingKind(..))
import           Data.Singletons.Prelude      (SingI (..))
import           Data.Singletons.Prelude.Enum (PEnum (..), SEnum (..))
import           Data.Singletons.Prelude.Ord  (POrd (..), SOrd (..))
import           Data.Singletons.TH           (sCases)
import           Data.Singletons.TypeLits     (withKnownNat)
import           Data.Type.Equality           ((:~:) (..))
import           Data.Type.Natural            (Nat (S, Z), Sing (SS, SZ))
import qualified Data.Type.Natural            as PN
import           Data.Void                    (absurd)
import           Data.Void                    (Void)
import           GHC.TypeLits                 (type (<=?))
import qualified GHC.TypeLits                 as TL
import           Language.Haskell.TH.Quote    (QuasiQuoter)
import           Proof.Equational             (coerce, withRefl)
import           Proof.Equational             (start, sym, (===), (=~=))
import           Proof.Equational             (because)
import           Proof.Propositional          (Empty (..), IsTrue (..),
                                               withEmpty, withWitness)
import           Unsafe.Coerce                (unsafeCoerce)

-- | Type synonym for @'PN.Nat'@ to avoid confusion with built-in @'TL.Nat'@.
type Peano = PN.Nat

type family FromPeano (n :: PN.Nat) :: TL.Nat where
  FromPeano 'Z = 0
  FromPeano ('S n) = Succ (FromPeano n)

type family ToPeano (n :: TL.Nat) :: PN.Nat where
  ToPeano 0 = 'Z
  ToPeano n = 'S (ToPeano (Pred n))

viewNat :: Sing (n :: TL.Nat) -> ZeroOrSucc n
viewNat n =
  case n %~ (sing :: Sing 0) of
    Proved Refl -> IsZero
    Disproved t -> withEmpty t $ IsSucc (sPred n)

sFromPeano :: Sing n -> Sing (FromPeano n)
sFromPeano SZ      = sing
sFromPeano (SS sn) = sSucc (sFromPeano sn)

toPeanoInjective :: forall n m. (TL.KnownNat n, TL.KnownNat m)
                 => ToPeano n :~: ToPeano m -> n :~: m
toPeanoInjective tPnEqtPm =
  let sn = sing :: Sing n
      sm = sing :: Sing m
  in start sn
       === sFromPeano (sToPeano sn) `because` sym (fromToPeano sn)
       === sFromPeano (sToPeano sm) `because` congFromPeano tPnEqtPm
       === sm                       `because` fromToPeano sm

-- trustMe :: a :~: b
-- trustMe = unsafeCoerce (Refl :: () :~: ())
-- {-# WARNING trustMe
--     "Used unproven type-equalities; This may cause disastrous result..." #-}

toPeanoSuccCong :: Sing n -> ToPeano (Succ n) :~: 'S (ToPeano n)
toPeanoSuccCong _ = unsafeCoerce (Refl :: () :~: ())
  -- We cannot prove this lemma within Haskell, so we assume it a priori.

infix 4 %<=?
(%<=?) :: Sing (n :: TL.Nat) -> Sing m -> Sing (n <=? m)
n %<=? m = case sCompare n m of
  SLT -> STrue
  SEQ -> STrue
  SGT -> SFalse

natLeqSuccEq :: Sing n -> Sing m -> ((n TL.+ 1) <=? (m TL.+ 1)) :~: (n <=? m)
natLeqSuccEq _ _ = Refl

leqqCong :: n :~: m -> l :~: z -> (n <=? l) :~: (m <=? z)
leqqCong Refl Refl = Refl

leqqAndLeq :: Sing n -> Sing m -> (n <=? m) :~: (n PN.<= m)
leqqAndLeq n m =
  case sCompare n m of
    SEQ -> Refl
    SLT -> Refl
    SGT -> Refl

natSuccPred :: forall n. TL.KnownNat n => ((n :~: 0) -> Void) -> Succ (Pred n) :~: n
natSuccPred refute =
  case sCompare (sing :: Sing 1) (sing :: Sing n) of
    SLT -> Refl
    SEQ -> Refl
    SGT -> absurd $ refute Refl

neqZero1leqq :: forall n. TL.KnownNat n => ((n :~: 0) -> Void) -> IsTrue (1 <=? n)
neqZero1leqq refute =
  case sCompare (sing :: Sing 1) (sing :: Sing n) of
    SLT -> Witness
    SEQ -> Witness
    SGT -> absurd $ refute Refl

sToPeano :: Sing n -> Sing (ToPeano n)
sToPeano sn =
  case sn %~ (sing :: Sing 0) of
    Proved eq     -> withRefl eq SZ
    Disproved _pf ->
      withKnownNat sn $
      withRefl (natSuccPred _pf) $
      coerce (sym (toPeanoSuccCong (sPred sn))) (SS (sToPeano (sPred sn)))

-- litSuccInjective :: forall (n :: TL.Nat) (m :: TL.Nat).
--                     Succ n :~: Succ m -> n :~: m
-- litSuccInjective Refl = Refl

toFromPeano :: Sing n -> ToPeano (FromPeano n) :~: n
toFromPeano SZ = Refl
toFromPeano (SS sn) =
  start (sToPeano (sFromPeano (SS sn)))
    =~= sToPeano (sSucc (sFromPeano sn))
    === SS (sToPeano (sFromPeano sn)) `because` toPeanoSuccCong (sFromPeano sn)
    === SS sn                         `because` succCong (toFromPeano sn)

congFromPeano :: n :~: m -> FromPeano n :~: FromPeano m
congFromPeano Refl = Refl

congToPeano :: n :~: m -> ToPeano n :~: ToPeano m
congToPeano Refl = Refl

congSucc :: n :~: m -> Succ n :~: Succ m
congSucc Refl = Refl

fromToPeano :: Sing n -> FromPeano (ToPeano n) :~: n
fromToPeano sn  =
  case viewNat sn of
    IsZero    -> Refl
    IsSucc n1 ->
      start (sFromPeano (sToPeano sn))
        =~= sFromPeano (sToPeano (sSucc n1))
        === sFromPeano (SS (sToPeano n1))
              `because` congFromPeano (toPeanoSuccCong n1)
        =~= sSucc (sFromPeano (sToPeano n1))
        === sSucc n1 `because` congSucc (fromToPeano n1)

fromPeanoInjective :: forall n m. (SingI n, SingI m)
                   => FromPeano n :~: FromPeano m -> n :~: m
fromPeanoInjective frEq =
  let sn = sing :: Sing n
      sm = sing :: Sing m
  in start sn
       === sToPeano (sFromPeano sn) `because` sym (toFromPeano sn)
       === sToPeano (sFromPeano sm) `because` congToPeano frEq
       === sm                       `because` toFromPeano sm

fromPeanoSuccCong :: Sing n -> FromPeano ('S n) :~: Succ (FromPeano n)
fromPeanoSuccCong _sn = Refl

fromPeanoPlusCong :: Sing n -> Sing m -> FromPeano (n PN.+ m) :~: FromPeano n TL.+ FromPeano m
fromPeanoPlusCong SZ _ = Refl
fromPeanoPlusCong (SS sn) sm =
  start (sFromPeano (SS sn %+ sm))
    =~= sFromPeano (SS (sn %+ sm))
    === sSucc (sFromPeano (sn %+ sm))           `because` fromPeanoSuccCong (sn %+ sm)
    === sSucc (sFromPeano sn  %+ sFromPeano sm) `because` congSucc (fromPeanoPlusCong sn sm)
    =~= sSucc (sFromPeano sn) %+ sFromPeano sm
    =~= sFromPeano (SS sn)    %+ sFromPeano sm

toPeanoPlusCong :: Sing n -> Sing m -> ToPeano (n TL.+ m) :~: ToPeano n PN.+ ToPeano m
toPeanoPlusCong sn sm =
  case viewNat sn of
    IsZero -> Refl
    IsSucc pn ->
      start (sToPeano (sSucc pn %+ sm))
        =~= sToPeano (sSucc (pn %+ sm))
        === SS (sToPeano (pn %+ sm))
            `because` toPeanoSuccCong (pn %+ sm)
        === SS (sToPeano pn %+ sToPeano sm)
            `because` succCong (toPeanoPlusCong pn sm)
        =~= SS (sToPeano pn) %+ sToPeano sm
        === (sToPeano (sSucc pn) %+ sToPeano sm)
            `because` plusCongL (sym (toPeanoSuccCong pn)) (sToPeano sm)
        =~= sToPeano sn %+ sToPeano sm

fromPeanoZeroCong :: FromPeano 'Z :~: 0
fromPeanoZeroCong = Refl

toPeanoZeroCong :: ToPeano 0 :~: 'Z
toPeanoZeroCong = Refl

fromPeanoOneCong :: FromPeano PN.One :~: 1
fromPeanoOneCong = Refl

toPeanoOneCong :: ToPeano 1 :~: PN.One
toPeanoOneCong = Refl

natPlusCongR :: Sing r -> n :~: m -> n TL.+ r :~: m TL.+ r
natPlusCongR _ Refl = Refl

fromPeanoMultCong :: Sing n -> Sing m -> FromPeano (n PN.* m) :~: FromPeano n TL.* FromPeano m
fromPeanoMultCong SZ _ = Refl
fromPeanoMultCong (SS psn) sm =
  start (sFromPeano (SS psn %* sm))
    =~= sFromPeano (psn %* sm %+ sm)
    === sFromPeano (psn %* sm) %+ sFromPeano sm
        `because` fromPeanoPlusCong (psn %* sm) sm
    === sFromPeano psn %* sFromPeano sm %+ sFromPeano sm
        `because` natPlusCongR (sFromPeano sm) (fromPeanoMultCong psn sm)
    =~= sSucc (sFromPeano psn) %* sFromPeano sm
    =~= sFromPeano (SS psn)    %* sFromPeano sm


toPeanoMultCong :: Sing n -> Sing m -> ToPeano (n TL.* m) :~: ToPeano n PN.* ToPeano m
toPeanoMultCong sn sm =
  case viewNat sn of
    IsZero -> Refl
    IsSucc psn ->
      start (sToPeano (sSucc psn %* sm))
        =~= sToPeano (psn %* sm %+ sm)
        === sToPeano (psn %* sm) %+ sToPeano sm
            `because` toPeanoPlusCong (psn %* sm) sm
        === sToPeano psn %* sToPeano sm %+ sToPeano sm
            `because` plusCongL (toPeanoMultCong psn sm) (sToPeano sm)
        =~= SS (sToPeano psn) %* sToPeano sm
        === sToPeano (sSucc psn) %* sToPeano sm
            `because` multCongL (sym (toPeanoSuccCong psn)) (sToPeano sm)
leqCong :: n :~: m -> l :~: z -> (n PN.<= l) :~: (m PN.<= z)
leqCong Refl Refl = Refl

fromPeanoMonotone :: ((n PN.<= m) ~ 'True) => Sing n -> Sing m -> (FromPeano n <=? FromPeano m) :~: 'True
fromPeanoMonotone SZ _ = Refl
fromPeanoMonotone (SS n) (SS m) =
   start (sFromPeano (SS n) %<=? sFromPeano (SS m))
     === (sSucc (sFromPeano n) %<=? sSucc (sFromPeano m))
      `because` leqqCong  (fromPeanoSuccCong n) (fromPeanoSuccCong m)
     === (sFromPeano n %<=? sFromPeano m)
      `because` natLeqSuccEq (sFromPeano n) (sFromPeano m)
     === STrue
      `because` fromPeanoMonotone n m
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
fromPeanoMonotone _ _ = bugInGHC
#endif

natLeqZero :: (n TL.<= 0) => Sing n -> n :~: 0
natLeqZero Zero = Refl
natLeqZero _    = error "natLeqZero : bug in ghc"

myLeqPred :: Sing n -> Sing m -> ('S n PN.<= 'S m) :~: (n PN.<= m)
myLeqPred SZ _          = Refl
myLeqPred (SS _) (SS _) = Refl
myLeqPred (SS _) SZ     = Refl

toPeanoCong :: a :~: b -> ToPeano a :~: ToPeano b
toPeanoCong Refl = Refl

toPeanoMonotone :: (n TL.<= m)
                => Sing n -> Sing m -> ((ToPeano n) PN.<= (ToPeano m)) :~: 'True
toPeanoMonotone sn sm =  withKnownNat sn $ withKnownNat sm $
  case sn %~ (sing :: Sing 0) of
    Proved eql -> withRefl eql Refl
    Disproved nPos -> withWitness (neqZero1leqq nPos) $ case sm %~ (sing :: Sing 0) of
      Proved mEq0 -> withRefl mEq0 $ absurd $ nPos $ natLeqZero sn
      Disproved mPos -> withWitness (neqZero1leqq mPos) $
        let pn = sPred sn
            pm = sPred sm
        in start (sToPeano sn %<= sToPeano sm)
             === (sToPeano (sSucc pn) %<= sToPeano (sSucc pm))
                 `because` leqCong (toPeanoCong $ sym $ natSuccPred nPos)
                                   (toPeanoCong $ sym $ natSuccPred mPos)
             === (SS (sToPeano pn) %<= SS (sToPeano pm))
                 `because` leqCong (toPeanoSuccCong pn) (toPeanoSuccCong pm)
             === (sToPeano pn %<= sToPeano pm)
                 `because` myLeqPred (sToPeano pn) (sToPeano pm)
             === STrue `because` toPeanoMonotone pn pm

-- | Induction scheme for built-in @'TL.Nat'@.
inductionNat :: forall p n. p 0 -> (forall m. p m -> p (m TL.+ 1)) -> Sing n -> p n
inductionNat base step sn =
  case viewNat sn of
    IsZero    -> base
    IsSucc sl -> step (inductionNat base step sl)


instance IsPeano TL.Nat where
  {-# SPECIALISE instance IsPeano TL.Nat #-}

  toNatural = fromIntegral . fromSing
  fromNatural = toSing . fromIntegral

  predSucc _ = Refl
  plusMinus _ _ = Refl
  succInj Refl = Refl
  succOneCong = Refl
  succNonCyclic _ a = case a of  _ -> error "Bug in GHC!"
  plusZeroR _ = Refl
  plusZeroL _ = Refl
  plusSuccL _ _ =  Refl
  plusSuccR _ _ =  Refl
  multZeroL _ = Refl
  multZeroR _ = Refl
  multSuccL _ _ = Refl
  multSuccR _ _ = Refl
  plusComm _ _ = Refl
  multComm _ _ = Refl
  plusAssoc _ _ _ = Refl
  multAssoc _ _ _ = Refl
  plusMultDistrib _ _ _ = Refl
  multPlusDistrib _ _ _ = Refl
  induction base step sn =
    case viewNat sn of
      IsZero    -> base
      IsSucc sl ->
        withKnownNat sl $ step sing (induction base step sl)

maxCompareFlip :: Sing n -> Sing m -> TL.CmpNat m n :~: 'LT -> Max n m :~: n
maxCompareFlip n m mLTn =
  case sCompare n m of
    SLT -> eliminate $
           start SLT === sCompare m n `because` sym mLTn
                     === sFlipOrdering (sCompare n m) `because` sym (flipCompare n m)
                     =~= SGT
    SEQ -> eliminate $
           start SLT === sCompare m n `because` sym mLTn
                     === sFlipOrdering (sCompare n m) `because` sym (flipCompare n m)
                     =~= SEQ
    SGT -> Refl

minCompareFlip :: Sing n -> Sing m -> TL.CmpNat m n :~: 'LT -> Min n m :~: m
minCompareFlip n m mLTn =
  case sCompare n m of
    SLT -> eliminate $
           start SLT === sCompare m n `because` sym mLTn
                     === sFlipOrdering (sCompare n m) `because` sym (flipCompare n m)
                     =~= SGT
    SEQ -> eliminate $
           start SLT === sCompare m n `because` sym mLTn
                     === sFlipOrdering (sCompare n m) `because` sym (flipCompare n m)
                     =~= SEQ
    SGT -> Refl

type family MyLeqHelper n m o where
  MyLeqHelper n m 'LT = 'True
  MyLeqHelper n m 'EQ = 'True
  MyLeqHelper n m 'GT = 'False

instance PeanoOrder TL.Nat where
  {-# SPECIALISE instance PeanoOrder TL.Nat #-}
  eqlCmpEQ _ _ Refl = Refl
  ltToLeq _ _ Refl = Witness
  succLeqToLT m n Witness =
    case sCompare (sSucc m) n of
      SLT -> Refl
      SEQ -> Refl
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
      _   -> bugInGHC
#endif
  cmpZero _ = Refl
  leqRefl _ = Witness
  eqToRefl _ _ Refl = Refl
  flipCompare n m = $(sCases ''Ordering [|sCompare n m|] [|Refl|])
  leqToCmp n m Witness =
    case sCompare n m of
      SLT -> Right Refl
      SEQ -> Left  Refl
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
      _   -> bugInGHC
#endif

  leqToMin _ _ Witness = Refl
  leqToMax _ _ Witness = Refl
  geqToMax n m mLEQn =
    case leqToCmp m n mLEQn of
      Left eql   -> withRefl eql Refl
      Right mLTn ->
        maxCompareFlip n m mLTn
  geqToMin n m mLEQn =
    case leqToCmp m n mLEQn of
      Left eql   -> withRefl eql Refl
      Right mLTn ->
        minCompareFlip n m mLTn

  lneqReversed n m =
    withRefl (flipCompare n m) $
      case sCompare n m of
        SEQ -> Refl
        SLT -> Refl
        SGT -> Refl

  leqReversed n m =
    withRefl (flipCompare n m) $
      case sCompare n m of
        SEQ -> Refl
        SLT -> Refl
        SGT -> Refl

  lneqSuccLeq n m =
    case sCompare n m of
      SEQ ->
        start (n %< m)
          =~= SFalse
          === (sSucc n %<= n) `because` sym (succLeqAbsurd' n)
          === (sSucc n %<= m) `because` sLeqCongR (sSucc n) (eqToRefl n m Refl)
      SLT -> withWitness (ltToSuccLeq n m Refl) $
        start (n %< m)
          =~= STrue
          =~= (sSucc n %<= m)
      SGT ->
        case sSucc n %<= m of
          SFalse -> Refl
          STrue  -> eliminate $ succLeqToLT n m Witness

-- instance Monomorphicable (Sing :: TL.Nat -> *) where
--   type MonomorphicRep (Sing :: TL.Nat -> *) = Integer
--   demote  (Monomorphic sn) = fromSing sn
--   {-# INLINE demote #-}

--   promote n = case toSing n of SomeSing k -> Monomorphic k
--   {-# INLINE promote #-}

-- | Quotesi-quoter for singleton types for @'GHC.TypeLits.Nat'@. This can be used for an expression.
--
--  For example: @[snat|12|] '%+' [snat| 5 |]@.
snat :: QuasiQuoter
snat = mkSNatQQ [t| TL.Nat |]

