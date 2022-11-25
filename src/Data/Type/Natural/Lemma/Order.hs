{-# LANGUAGE DataKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Data.Type.Natural.Lemma.Order
  ( DiffNat (..),
    LeqView (..),
    type (<),
    type (<?),
    (%<?),
    type (>),
    type (>?),
    (%>?),
    type (>=),
    type (>=?),
    (%>=?),
    FlipOrdering,
    Min,
    sMin,
    Max,
    sMax,
    OrdCond,
    sOrdCond,

    -- * Lemmas
    ordCondDistrib,
    leqOrdCond,
    sFlipOrdering,
    coerceLeqL,
    coerceLeqR,
    sLeqCongL,
    sLeqCongR,
    sLeqCong,
    succDiffNat,
    compareCongR,
    leqToCmp,
    eqlCmpEQ,
    eqToRefl,
    flipCmpNat,
    ltToNeq,
    leqNeqToLT,
    succLeqToLT,
    ltToLeq,
    gtToLeq,
    congFlipOrdering,
    ltToSuccLeq,
    cmpZero,
    cmpSuccZeroGT,
    leqToGT,
    cmpZero',
    zeroNoLT,
    ltRightPredSucc,
    cmpSucc,
    ltSucc,
    cmpSuccStepR,
    ltSuccLToLT,
    leqToLT,
    leqZero,
    leqSucc,
    fromLeqView,
    leqViewRefl,
    viewLeq,
    leqWitness,
    leqStep,
    leqNeqToSuccLeq,
    leqRefl,
    leqSuccStepR,
    leqSuccStepL,
    leqReflexive,
    leqTrans,
    leqAntisymm,
    plusMonotone,
    leqZeroElim,
    plusMonotoneL,
    plusMonotoneR,
    plusLeqL,
    plusLeqR,
    plusCancelLeqR,
    plusCancelLeqL,
    succLeqZeroAbsurd,
    succLeqZeroAbsurd',
    succLeqAbsurd,
    succLeqAbsurd',
    notLeqToLeq,
    leqSucc',
    leqToMin,
    geqToMin,
    minComm,
    minLeqL,
    minLeqR,
    minLargest,
    leqToMax,
    geqToMax,
    maxComm,
    maxLeqR,
    maxLeqL,
    maxLeast,
    lneqSuccLeq,
    lneqReversed,
    lneqToLT,
    ltToLneq,
    lneqZero,
    lneqSucc,
    succLneqSucc,
    lneqRightPredSucc,
    lneqSuccStepL,
    lneqSuccStepR,
    plusStrictMonotone,
    minCase,
    maxCase,
    maxZeroL,
    maxZeroR,
    minZeroL,
    minZeroR,
    minusSucc,
    lneqZeroAbsurd,
    minusPlus,
    minPlusTruncMinus,
    truncMinusLeq,
    type (-.),
    (%-.),

    -- * Various witnesses for orderings
    LeqWitness,
    (:<:),
    Leq (..),
    leqRhs,
    leqLhs,

    -- ** conversions between lax orders
    propToBoolLeq,
    boolToPropLeq,

    -- ** conversions between strict orders
    propToBoolLt,
    boolToPropLt,
  )
where

import Data.Coerce (coerce)
import Data.Type.Equality (gcastWith, (:~:) (..))
import Data.Type.Natural.Core
import Data.Type.Natural.Lemma.Arithmetic
import Data.Void (Void, absurd)
import Numeric.Natural (Natural)
import Proof.Equational
  ( because,
    start,
    sym,
    trans,
    (===),
    (=~=),
  )
import Proof.Propositional (IsTrue (..), eliminate, withWitness)
#if MIN_VERSION_ghc(9,2,1)
import qualified Data.Type.Ord as DTO
import Data.Type.Ord (OrdCond)
#endif


--------------------------------------------------

-- ** Type-level predicate & judgements.

--------------------------------------------------

#if !MIN_VERSION_ghc(9,2,1)
type family OrdCond (o :: Ordering) (lt :: k) (eq :: k) (gt :: k) where
  OrdCond 'LT lt eq gt = lt
  OrdCond 'EQ lt eq gt = eq
  OrdCond 'GT lt eq gt = gt
#endif

sOrdCond :: SOrdering o -> f lt -> f eq -> f gt -> f (OrdCond o lt eq gt)
sOrdCond SLT lt _ _ = lt
sOrdCond SEQ _ eq _ = eq
sOrdCond SGT _ _ gt = gt

minCase :: SNat n -> SNat m -> Either (Min n m :~: n) (Min n m :~: m)
minCase n m =
  case sCmpNat n m of
    SLT -> Left Refl
    SEQ -> Left Refl
    SGT -> Right Refl

maxCase :: SNat n -> SNat m -> Either (Max n m :~: m) (Max n m :~: n)
maxCase n m =
  case sCmpNat n m of
    SLT -> Left Refl
    SEQ -> Left Refl
    SGT -> Right Refl

-- | Comparison via GADTs.
data Leq n m where
  ZeroLeq :: SNat m -> Leq 0 m
  SuccLeqSucc :: Leq n m -> Leq (n + 1) (m + 1)

type LeqWitness n m = IsTrue (n <=? m)

-- | Since 1.2.0 (argument changed)
data a :<: b where
  ZeroLtSucc :: SNat m -> 0 :<: (m + 1)
  SuccLtSucc :: SNat n -> SNat m -> n :<: m -> (n + 1) :<: (m + 1)

deriving instance Show (a :<: b)

--------------------------------------------------

-- * Total orderings on natural numbers.

--------------------------------------------------
propToBoolLeq :: forall n m. Leq n m -> LeqWitness n m
propToBoolLeq (ZeroLeq _) = Witness
propToBoolLeq (SuccLeqSucc leq) = withWitness (propToBoolLeq leq) Witness
{-# INLINE propToBoolLeq #-}

boolToPropLeq :: (n <= m) => SNat n -> SNat m -> Leq n m
boolToPropLeq Zero m = ZeroLeq m
boolToPropLeq (Succ n) (Succ m) = SuccLeqSucc $ boolToPropLeq n m
boolToPropLeq (Succ n) Zero = absurd $ succLeqZeroAbsurd n Witness

leqRhs :: Leq n m -> SNat m
leqRhs (ZeroLeq m) = m
leqRhs (SuccLeqSucc leq) = sSucc $ leqRhs leq

leqLhs :: Leq n m -> SNat n
leqLhs (ZeroLeq _) = Zero
leqLhs (SuccLeqSucc leq) = sSucc $ leqLhs leq

propToBoolLt :: n :<: m -> IsTrue (n <? m)
propToBoolLt (ZeroLtSucc (sm :: SNat m)) = 
  gcastWith (cmpZero sm) Witness
propToBoolLt (SuccLtSucc sn sm lt) =
  gcastWith (cmpSucc sn sm) $
  withWitness (propToBoolLt lt) Witness

boolToPropLt :: n < m => SNat n -> SNat m -> n :<: m
boolToPropLt Zero (Succ sn) = ZeroLtSucc sn
boolToPropLt (Succ n) Zero = eliminate $
  start STrue
  =~= (Succ n %<? Zero)
  =~= sOrdCond (sCmpNat (Succ n) Zero) STrue SFalse SFalse
  === sOrdCond SGT STrue SFalse SFalse
    `because` sOrdCondCong1 (cmpSuccZeroGT n) STrue SFalse SFalse
  =~= SFalse
boolToPropLt (Succ n) (Succ m) = 
  gcastWith (cmpSucc n m) $
  SuccLtSucc n m (boolToPropLt n m)

#if MIN_VERSION_ghc(9,2,1)
type Min m n = DTO.Min @Nat m n
#else
type Min m n = OrdCond (CmpNat m n) m m n
#endif

sMin :: SNat n -> SNat m -> SNat (Min n m)
sMin = coerce $ min @Natural

sMax :: SNat n -> SNat m -> SNat (Max n m)
sMax = coerce $ max @Natural

#if MIN_VERSION_ghc(9,2,1)
type Max m n = DTO.Max @Nat m n
#else
type Max m n = OrdCond (CmpNat m n) n n m
#endif

infix 4 <?, <, >=?, >=, >, >?

#if MIN_VERSION_ghc(9,2,1)
type (n :: Nat) <? m = n DTO.<? m
#else
type n <? m = OrdCond (CmpNat n m) 'True 'False 'False
#endif

(%<?) :: SNat n -> SNat m -> SBool (n <? m)
n %<? m = sOrdCond (sCmpNat n m) STrue SFalse SFalse

#if MIN_VERSION_ghc(9,2,2)
type (n :: Nat) < m = n DTO.< m
#else
type n < m = (n <? m) ~ 'True
#endif

#if MIN_VERSION_ghc(9,2,1)
type n >=? m = (DTO.>=?) @Nat n m
#else
type n >=? m = OrdCond (CmpNat n m) 'False 'True 'True
#endif

(%>=?) :: SNat n -> SNat m -> SBool (n >=? m)
n %>=? m = sOrdCond (sCmpNat n m) SFalse STrue STrue

#if MIN_VERSION_ghc(9,2,1)
type (n :: Nat) >= m = n DTO.>= m
#else
type n >= m = (n >=? m) ~ 'True
#endif

#if MIN_VERSION_ghc(9,2,1)
type (n :: Nat) >? m = n DTO.>? m
#else
type n >? m = OrdCond (CmpNat n m) 'False 'False 'True
#endif

(%>?) :: SNat n -> SNat m -> SBool (n >? m)
n %>? m = sOrdCond (sCmpNat n m) SFalse SFalse STrue

#if MIN_VERSION_ghc(9,2,1)
type (n :: Nat) > m = n DTO.> m
#else
type n > m = (n >? m) ~ 'True
#endif

infix 4 %>?, %<?, %>=?

ordCondDistrib :: proxy f -> SOrdering o -> p l -> p' e -> p'' g ->
  OrdCond o (f l) (f e) (f g) :~: f (OrdCond o l e g)
ordCondDistrib _ SLT _ _ _ = Refl
ordCondDistrib _ SEQ _ _ _ = Refl
ordCondDistrib _ SGT _ _ _ = Refl

leqOrdCond
  :: SNat n -> SNat m -> (n <=? m) :~: OrdCond (CmpNat n m) 'True 'True 'False
#if MIN_VERSION_ghc(9,2,1)
leqOrdCond _ _ = Refl
#else
leqOrdCond Zero n =
  case cmpZero' n of
    Left Refl -> Refl
    Right Refl -> Refl
leqOrdCond (Succ m) Zero = 
  gcastWith (succLeqZeroAbsurd' m) $
  gcastWith (cmpSuccZeroGT m) $
  Refl
leqOrdCond (Succ m) (Succ n) =
  gcastWith (cmpSucc m n) $
  start (Succ m %<=? Succ n)
  === (m %<=? n) `because` sym (leqSucc' m n)
  === sOrdCond (sCmpNat m n) STrue STrue SFalse `because` leqOrdCond m n
#endif

data LeqView n m where
  LeqZero :: SNat n -> LeqView 0 n
  LeqSucc :: SNat n -> SNat m -> IsTrue (n <=? m) -> LeqView (Succ n) (Succ m)

data DiffNat n m where
  DiffNat :: SNat n -> SNat m -> DiffNat n (n + m)

newtype LeqWitPf n = LeqWitPf {leqWitPf :: forall m. SNat m -> IsTrue (n <=? m) -> DiffNat n m}

succDiffNat :: SNat n -> SNat m -> DiffNat n m -> DiffNat (Succ n) (Succ m)
succDiffNat _ _ (DiffNat n m) = gcastWith (plusSuccL n m) $ DiffNat (sSucc n) m

-- | Since 1.0.0.0 (type changed)
coerceLeqL ::
  forall n m l.
  n :~: m ->
  SNat l ->
  IsTrue (n <=? l) ->
  IsTrue (m <=? l)
coerceLeqL Refl _ Witness = Witness

-- | Since 1.0.0.0 (type changed)
coerceLeqR ::
  forall n m l.
  SNat l ->
  n :~: m ->
  IsTrue (l <=? n) ->
  IsTrue (l <=? m)
coerceLeqR _ Refl Witness = Witness

compareCongR :: SNat a -> b :~: c -> CmpNat a b :~: CmpNat a c
compareCongR _ Refl = Refl

sLeqCong :: a :~: b -> c :~: d -> (a <= c) :~: (b <= d)
sLeqCong Refl Refl = Refl

sLeqCongL :: a :~: b -> SNat c -> (a <= c) :~: (b <= c)
sLeqCongL Refl _ = Refl

sLeqCongR :: SNat a -> b :~: c -> (a <= b) :~: (a <= c)
sLeqCongR _ Refl = Refl

newtype LeqViewRefl n = LeqViewRefl {proofLeqViewRefl :: LeqView n n}

leqToCmp ::
  SNat a ->
  SNat b ->
  IsTrue (a <=? b) ->
  Either (a :~: b) (CmpNat a b :~: 'LT)
leqToCmp n m Witness =
  case n %~ m of
    Equal -> Left Refl
    NonEqual -> Right Refl

eqlCmpEQ :: SNat a -> SNat b -> a :~: b -> CmpNat a b :~: 'EQ
eqlCmpEQ _ _ Refl = Refl

eqToRefl :: SNat a -> SNat b -> CmpNat a b :~: 'EQ -> a :~: b
eqToRefl _ _ Refl = Refl

flipCmpNat ::
  SNat a ->
  SNat b ->
  FlipOrdering (CmpNat a b) :~: CmpNat b a
flipCmpNat n m = case sCmpNat n m of
  SGT -> Refl
  SLT -> Refl
  SEQ -> Refl

ltToNeq ::
  SNat a ->
  SNat b ->
  CmpNat a b :~: 'LT ->
  a :~: b ->
  Void
ltToNeq a b aLTb aEQb =
  eliminate $
    start SLT
      === sCmpNat a b `because` sym aLTb
      === SEQ `because` eqlCmpEQ a b aEQb

leqNeqToLT :: SNat a -> SNat b -> IsTrue (a <=? b) -> (a :~: b -> Void) -> CmpNat a b :~: 'LT
leqNeqToLT a b aLEQb aNEQb = either (absurd . aNEQb) id $ leqToCmp a b aLEQb

succLeqToLT :: SNat a -> SNat b -> IsTrue (S a <=? b) -> CmpNat a b :~: 'LT
succLeqToLT _ _ Witness = Refl

ltToLeq ::
  SNat a ->
  SNat b ->
  CmpNat a b :~: 'LT ->
  IsTrue (a <=? b)
ltToLeq _ _ Refl = Witness

gtToLeq ::
  SNat a ->
  SNat b ->
  CmpNat a b :~: 'GT ->
  IsTrue (b <=? a)
gtToLeq _ _ Refl = Witness

congFlipOrdering ::
  a :~: b -> FlipOrdering a :~: FlipOrdering b
congFlipOrdering Refl = Refl

ltToSuccLeq ::
  SNat a ->
  SNat b ->
  CmpNat a b :~: 'LT ->
  IsTrue (Succ a <=? b)
ltToSuccLeq _ _ Refl = Witness

cmpZero :: SNat a -> CmpNat 0 (Succ a) :~: 'LT
cmpZero _ = Refl

cmpSuccZeroGT :: SNat a -> CmpNat (Succ a) 0 :~: 'GT
cmpSuccZeroGT _ = Refl

leqToGT ::
  SNat a ->
  SNat b ->
  IsTrue (Succ b <=? a) ->
  CmpNat a b :~: 'GT
leqToGT _ _ Witness = Refl

cmpZero' :: SNat a -> Either (CmpNat 0 a :~: 'EQ) (CmpNat 0 a :~: 'LT)
cmpZero' n =
  case zeroOrSucc n of
    IsZero -> Left $ eqlCmpEQ sZero n Refl
    IsSucc n' -> Right $ cmpZero n'

zeroNoLT :: SNat a -> CmpNat a 0 :~: 'LT -> Void
zeroNoLT n eql =
  case cmpZero' n of
    Left cmp0nEQ ->
      eliminate $
        start SGT
          =~= sFlipOrdering SLT
          === sFlipOrdering (sCmpNat n sZero) `because` congFlipOrdering (sym eql)
          === sCmpNat sZero n `because` flipCmpNat n sZero
          === SEQ `because` cmp0nEQ
    Right cmp0nLT ->
      eliminate $
        start SGT
          =~= sFlipOrdering SLT
          === sFlipOrdering (sCmpNat n sZero) `because` congFlipOrdering (sym eql)
          === sCmpNat sZero n `because` flipCmpNat n sZero
          === SLT `because` cmp0nLT

ltRightPredSucc :: SNat a -> SNat b -> CmpNat a b :~: 'LT -> b :~: Succ (Pred b)
ltRightPredSucc _ _ Refl = Refl

cmpSucc :: SNat n -> SNat m -> CmpNat n m :~: CmpNat (Succ n) (Succ m)
cmpSucc _ _ = Refl

ltSucc :: SNat a -> CmpNat a (Succ a) :~: 'LT
ltSucc _ = Refl

cmpSuccStepR ::
  forall n m.
  SNat n ->
  SNat m ->
  CmpNat n m :~: 'LT ->
  CmpNat n (Succ m) :~: 'LT
cmpSuccStepR _ _ Refl = Refl

ltSuccLToLT ::
  SNat n ->
  SNat m ->
  CmpNat (Succ n) m :~: 'LT ->
  CmpNat n m :~: 'LT
ltSuccLToLT n m snLTm =
  case zeroOrSucc m of
    IsZero -> absurd $ zeroNoLT (sSucc n) snLTm
    IsSucc m' ->
      let nLTm = cmpSucc n m' `trans` snLTm
       in start (sCmpNat n (sSucc m'))
            === SLT `because` cmpSuccStepR n m' nLTm

leqToLT ::
  SNat a ->
  SNat b ->
  IsTrue (Succ a <=? b) ->
  CmpNat a b :~: 'LT
leqToLT _ _ Witness = Refl

leqZero :: SNat n -> IsTrue (0 <=? n)
leqZero _ = Witness

leqSucc :: SNat n -> SNat m -> IsTrue (n <=? m) -> IsTrue (Succ n <=? Succ m)
leqSucc _ _ Witness = Witness

fromLeqView :: LeqView n m -> IsTrue (n <=? m)
fromLeqView (LeqZero n) = leqZero n
fromLeqView (LeqSucc n m nLEQm) = leqSucc n m nLEQm

leqViewRefl :: SNat n -> LeqView n n
leqViewRefl = proofLeqViewRefl . induction base step
  where
    base :: LeqViewRefl 0
    base = LeqViewRefl $ LeqZero sZero
    step :: SNat n -> LeqViewRefl n -> LeqViewRefl (Succ n)
    step n (LeqViewRefl nLEQn) =
      LeqViewRefl $ LeqSucc n n (fromLeqView nLEQn)

viewLeq :: forall n m. SNat n -> SNat m -> IsTrue (n <=? m) -> LeqView n m
viewLeq n m nLEQm =
  case (zeroOrSucc n, leqToCmp n m nLEQm) of
    (IsZero, _) -> LeqZero m
    (_, Left Refl) -> leqViewRefl n
    (IsSucc n', Right nLTm) ->
      let sm'EQm = ltRightPredSucc n m nLTm
          m' = sPred m
          n'LTm' = cmpSucc n' m' `trans` compareCongR n (sym sm'EQm) `trans` nLTm
       in gcastWith (sym sm'EQm) $ LeqSucc n' m' $ ltToLeq n' m' n'LTm'

leqWitness :: forall n m. SNat n -> SNat m -> IsTrue (n <=? m) -> DiffNat n m
leqWitness = \sn -> leqWitPf (induction base step sn) @m
  where
    base :: LeqWitPf 0
    base = LeqWitPf $ \sm _ -> gcastWith (plusZeroL sm) $ DiffNat sZero sm

    step :: SNat x -> LeqWitPf x -> LeqWitPf (Succ x)
    step (n :: SNat x) (LeqWitPf ih) = LeqWitPf $ \m snLEQm ->
      case viewLeq (sSucc n) m snLEQm of
#if !MIN_VERSION_ghc(9,2,0) || MIN_VERSION_ghc(9,4,0)
        LeqZero _ -> absurd $ succNonCyclic n Refl
#endif
        LeqSucc (_ :: SNat n') pm nLEQpm ->
          succDiffNat n pm $ ih pm $ coerceLeqL (succInj Refl :: n' :~: x) pm nLEQpm

leqStep :: forall n m l. SNat n -> SNat m -> SNat l -> n + l :~: m -> IsTrue (n <=? m)
leqStep _ _ _ Refl = Witness

leqNeqToSuccLeq :: SNat n -> SNat m -> IsTrue (n <=? m) -> (n :~: m -> Void) -> IsTrue (Succ n <=? m)
leqNeqToSuccLeq n m nLEQm nNEQm =
  case leqWitness n m nLEQm of
    DiffNat _ k ->
      case zeroOrSucc k of
        IsZero -> absurd $ nNEQm $ sym $ plusZeroR n
        IsSucc k' ->
          leqStep (sSucc n) m k' $
            start (sSucc n %+ k')
              === sSucc (n %+ k') `because` plusSuccL n k'
              === n %+ sSucc k' `because` sym (plusSuccR n k')
              =~= m

leqRefl :: SNat n -> IsTrue (n <=? n)
leqRefl _ = Witness

leqSuccStepR :: SNat n -> SNat m -> IsTrue (n <=? m) -> IsTrue (n <=? Succ m)
leqSuccStepR _ _ Witness = Witness

leqSuccStepL :: SNat n -> SNat m -> IsTrue (Succ n <=? m) -> IsTrue (n <=? m)
leqSuccStepL _ _ Witness = Witness

leqReflexive :: SNat n -> SNat m -> n :~: m -> IsTrue (n <=? m)
leqReflexive _ _ Refl = Witness

leqTrans :: SNat n -> SNat m -> SNat l -> IsTrue (n <=? m) -> IsTrue (m <=? l) -> IsTrue (n <=? l)
leqTrans _ _ _ Witness Witness = Witness

leqAntisymm :: SNat n -> SNat m -> IsTrue (n <=? m) -> IsTrue (m <=? n) -> n :~: m
leqAntisymm _ _ Witness Witness = Refl

plusMonotone ::
  SNat n ->
  SNat m ->
  SNat l ->
  SNat k ->
  IsTrue (n <=? m) ->
  IsTrue (l <=? k) ->
  IsTrue ((n + l) <=? (m + k))
plusMonotone _ _ _ _ Witness Witness = Witness

leqZeroElim :: SNat n -> IsTrue (n <=? 0) -> n :~: 0
leqZeroElim _ Witness = Refl

plusMonotoneL ::
  SNat n ->
  SNat m ->
  SNat l ->
  IsTrue (n <=? m) ->
  IsTrue ((n + l) <=? (m + l))
plusMonotoneL _ _ _ Witness = Witness

plusMonotoneR ::
  SNat n ->
  SNat m ->
  SNat l ->
  IsTrue (m <=? l) ->
  IsTrue ((n + m) <=? (n + l))
plusMonotoneR _ _ _ Witness = Witness

plusLeqL :: SNat n -> SNat m -> IsTrue (n <=? (n + m))
plusLeqL _ _  = Witness

plusLeqR :: SNat n -> SNat m -> IsTrue (m <=? (n + m))
plusLeqR _ _ = Witness

plusCancelLeqR ::
  SNat n ->
  SNat m ->
  SNat l ->
  IsTrue ((n + l) <=? (m + l)) ->
  IsTrue (n <=? m)
plusCancelLeqR _ _ _ Witness = Witness

plusCancelLeqL ::
  SNat n ->
  SNat m ->
  SNat l ->
  IsTrue ((n + m) <=? (n + l)) ->
  IsTrue (m <=? l)
plusCancelLeqL _ _ _ Witness = Witness

succLeqZeroAbsurd :: SNat n -> IsTrue (S n <=? 0) -> Void
succLeqZeroAbsurd n leq =
  succNonCyclic n (leqZeroElim (sSucc n) leq)

succLeqZeroAbsurd' :: SNat n -> (S n <=? 0) :~: 'False
succLeqZeroAbsurd' _ = Refl

succLeqAbsurd :: SNat n -> IsTrue (S n <=? n) -> Void
succLeqAbsurd n snLEQn =
  eliminate $
    start SLT
      === sCmpNat n n `because` sym (succLeqToLT n n snLEQn)
      === SEQ `because` eqlCmpEQ n n Refl

succLeqAbsurd' :: SNat n -> (S n <=? n) :~: 'False
succLeqAbsurd' _ = Refl

notLeqToLeq :: forall n m. ((n <=? m) ~ 'False) => SNat n -> SNat m -> IsTrue (m <=? n)
notLeqToLeq _ _ = Witness

leqSucc' :: SNat n -> SNat m -> (n <=? m) :~: (Succ n <=? Succ m)
leqSucc' _ _ = Refl

leqToMin :: SNat n -> SNat m -> IsTrue (n <=? m) -> Min n m :~: n
leqToMin n m Witness =
  case leqToCmp n m Witness of
    Left Refl -> Refl
    Right Refl -> Refl

geqToMin :: SNat n -> SNat m -> IsTrue (m <=? n) -> Min n m :~: m
geqToMin n m Witness =
  case leqToCmp m n Witness of
    Left Refl -> Refl
    Right Refl -> 
      gcastWith (flipCmpNat m n) Refl

minComm :: SNat n -> SNat m -> Min n m :~: Min m n
minComm n m =
  case n %<=? m of
    STrue ->
      start (sMin n m) === n `because` leqToMin n m Witness
        === sMin m n `because` sym (geqToMin m n Witness)
    SFalse ->
      start (sMin n m) === m `because` geqToMin n m (notLeqToLeq n m)
        === sMin m n `because` sym (leqToMin m n $ notLeqToLeq n m)

minLeqL :: SNat n -> SNat m -> IsTrue (Min n m <=? n)
minLeqL n m =
  case n %<=? m of
    STrue -> leqReflexive (sMin n m) n $ leqToMin n m Witness
    SFalse ->
      let mLEQn = notLeqToLeq n m
       in leqTrans
            (sMin n m)
            m
            n
            (leqReflexive (sMin n m) m (geqToMin n m mLEQn))
            $ mLEQn

minLeqR :: SNat n -> SNat m -> IsTrue (Min n m <=? m)
minLeqR n m =
  leqTrans
    (sMin n m)
    (sMin m n)
    m
    (leqReflexive (sMin n m) (sMin m n) $ minComm n m)
    (minLeqL m n)

minLargest ::
  SNat l ->
  SNat n ->
  SNat m ->
  IsTrue (l <=? n) ->
  IsTrue (l <=? m) ->
  IsTrue (l <=? Min n m)
minLargest _ n m lLEQn lLEQm =
  case minCase n m of
    Left Refl -> lLEQn
    Right Refl -> lLEQm

leqToMax :: SNat n -> SNat m -> IsTrue (n <=? m) -> Max n m :~: m
leqToMax n m lLeqm =
  case leqToCmp n m lLeqm of
    Left Refl -> Refl
    Right Refl -> Refl

geqToMax :: SNat n -> SNat m -> IsTrue (m <=? n) -> Max n m :~: n
geqToMax n m Witness =
  case sCmpNat n m of
    SLT -> Refl
    SEQ -> Refl
    SGT -> Refl

maxComm :: SNat n -> SNat m -> Max n m :~: Max m n
maxComm n m =
  case n %<=? m of
    STrue ->
      start (sMax n m) === m `because` leqToMax n m Witness
        === sMax m n `because` sym (geqToMax m n Witness)
    SFalse ->
      start (sMax n m) === n `because` geqToMax n m (notLeqToLeq n m)
        === sMax m n `because` sym (leqToMax m n $ notLeqToLeq n m)

maxLeqR :: SNat n -> SNat m -> IsTrue (m <=? Max n m)
maxLeqR n m =
  case n %<=? m of
    STrue -> leqReflexive m (sMax n m) $ sym $ leqToMax n m Witness
    SFalse ->
      let mLEQn = notLeqToLeq n m
       in leqTrans
            m
            n
            (sMax n m)
            mLEQn
            (leqReflexive n (sMax n m) (sym $ geqToMax n m mLEQn))

maxLeqL :: SNat n -> SNat m -> IsTrue (n <=? Max n m)
maxLeqL n m =
  leqTrans
    n
    (sMax m n)
    (sMax n m)
    (maxLeqR m n)
    (leqReflexive (sMax m n) (sMax n m) $ maxComm m n)

maxLeast ::
  SNat l ->
  SNat n ->
  SNat m ->
  IsTrue (n <=? l) ->
  IsTrue (m <=? l) ->
  IsTrue (Max n m <=? l)
maxLeast _ n m nLEQl mLEQl =
  case maxCase n m of
    Left Refl -> mLEQl
    Right Refl -> nLEQl


-- | Since 1.2.0.0 (type changed)
lneqSuccLeq :: SNat n -> SNat m -> (n <? m) :~: (Succ n <=? m)
#if MIN_VERSION_ghc(9,2,1)
lneqSuccLeq _ _ = Refl
#else
lneqSuccLeq n m = isTrueRefl (n %<? m) (Succ n %<=? m)
  (ltToSuccLeq n m . lneqToLT n m)
  (ltToLneq n m . succLeqToLT n m)

isTrueRefl :: SBool a -> SBool b 
  -> (IsTrue a -> IsTrue b)
  -> (IsTrue b -> IsTrue a)
  -> a :~: b
isTrueRefl SFalse SFalse _ _ = Refl
isTrueRefl STrue _ f _ = withWitness (f Witness) Refl
isTrueRefl _ STrue _ g = withWitness (g Witness) Refl
#endif

-- | Since 1.2.0.0 (type changed)
lneqReversed :: SNat n -> SNat m -> (n <? m) :~: (m >? n)
#if MIN_VERSION_ghc(9,2,1)
lneqReversed _ _ = Refl
#else
lneqReversed n m = 
  case sCmpNat n m of
    SLT -> gcastWith (flipCmpNat n m) Refl
    SEQ -> gcastWith (flipCmpNat n m) Refl
    SGT -> gcastWith (flipCmpNat n m) Refl
#endif

lneqToLT ::
  SNat n ->
  SNat m ->
  IsTrue (n <? m) ->
  CmpNat n m :~: 'LT
lneqToLT n m Witness =
  case sCmpNat n m of
    SLT -> Refl

ltToLneq ::
  SNat n ->
  SNat m ->
  CmpNat n m :~: 'LT ->
  IsTrue (n <? m)
ltToLneq _ _ Refl = Witness

lneqZero :: SNat a -> IsTrue (0 <? Succ a)
lneqZero n = ltToLneq sZero (sSucc n) $ cmpZero n

lneqSucc :: SNat n -> IsTrue (n <? Succ n)
lneqSucc n = ltToLneq n (sSucc n) $ ltSucc n

succLneqSucc ::
  SNat n ->
  SNat m ->
  (n <? m) :~: (Succ n <? Succ m)
succLneqSucc n m = 
  start (n %<? m)
  =~=
  sOrdCond (sCmpNat n m)  STrue SFalse SFalse
  === sOrdCond (sCmpNat (Succ n) (Succ m)) STrue SFalse SFalse 
    `because` sOrdCondCong1 (cmpSucc n m) STrue SFalse SFalse
  =~= (Succ n %<? Succ m)

sOrdCondCong1 :: o :~: o' -> proxy a -> proxy' b -> proxy' c 
  -> OrdCond o a b c :~: OrdCond o' a b c
sOrdCondCong1 Refl _ _ _ = Refl

lneqRightPredSucc ::
  SNat n ->
  SNat m ->
  IsTrue (n <? m) ->
  m :~: Succ (Pred m)
lneqRightPredSucc n m nLNEQm = ltRightPredSucc n m $ lneqToLT n m nLNEQm

lneqSuccStepL :: SNat n -> SNat m -> IsTrue (Succ n <? m) -> IsTrue (n <? m)
lneqSuccStepL n m snLNEQm =
  gcastWith (sym $ lneqSuccLeq n m) $
    leqSuccStepL (sSucc n) m $
      gcastWith (lneqSuccLeq (sSucc n) m) snLNEQm

lneqSuccStepR :: SNat n -> SNat m -> IsTrue (n <? m) -> IsTrue (n <? Succ m)
lneqSuccStepR n m nLNEQm =
  gcastWith (sym $ lneqSuccLeq n (sSucc m)) $
    leqSuccStepR (sSucc n) m $
      gcastWith (lneqSuccLeq n m) nLNEQm

plusStrictMonotone ::
  SNat n ->
  SNat m ->
  SNat l ->
  SNat k ->
  IsTrue (n <? m) ->
  IsTrue (l <? k) ->
  IsTrue ((n + l) <? (m + k))
plusStrictMonotone n m l k nLNm lLNk =
  gcastWith (sym $ lneqSuccLeq (n %+ l) (m %+ k)) $
    flip coerceLeqL (m %+ k) (plusSuccL n l) $
      plusMonotone
        (sSucc n)
        m
        l
        k
        (gcastWith (lneqSuccLeq n m) nLNm)
        ( leqTrans l (sSucc l) k (leqSuccStepR l l (leqRefl l)) $
            gcastWith (lneqSuccLeq l k) lLNk
        )

maxZeroL :: SNat n -> Max 0 n :~: n
maxZeroL n = leqToMax sZero n (leqZero n)

maxZeroR :: SNat n -> Max n 0 :~: n
maxZeroR n = geqToMax n sZero (leqZero n)

minZeroL :: SNat n -> Min 0 n :~: 0
minZeroL n = leqToMin sZero n (leqZero n)

minZeroR :: SNat n -> Min n 0 :~: 0
minZeroR n = geqToMin n sZero (leqZero n)

minusSucc :: SNat n -> SNat m -> IsTrue (m <=? n) -> Succ n - m :~: Succ (n - m)
minusSucc n m mLEQn =
  case leqWitness m n mLEQn of
    DiffNat _ k ->
      start (sSucc n %- m)
        =~= sSucc (m %+ k) %- m
        === (m %+ sSucc k) %- m `because` minusCongL (sym $ plusSuccR m k) m
        === (sSucc k %+ m) %- m `because` minusCongL (plusComm m (sSucc k)) m
        === sSucc k `because` plusMinus (sSucc k) m
        === sSucc (k %+ m %- m) `because` succCong (sym $ plusMinus k m)
        === sSucc (m %+ k %- m) `because` succCong (minusCongL (plusComm k m) m)
        =~= sSucc (n %- m)

lneqZeroAbsurd :: SNat n -> IsTrue (n <? 0) -> Void
lneqZeroAbsurd n leq =
  succLeqZeroAbsurd n (gcastWith (lneqSuccLeq n sZero) leq)

minusPlus ::
  forall n m.
  SNat n ->
  SNat m ->
  IsTrue (m <=? n) ->
  n - m + m :~: n
minusPlus n m mLEQn =
  case leqWitness m n mLEQn of
    DiffNat _ k ->
      start (n %- m %+ m)
        =~= m %+ k %- m %+ m
        === k %+ m %- m %+ m `because` plusCongL (minusCongL (plusComm m k) m) m
        === k %+ m `because` plusCongL (plusMinus k m) m
        === m %+ k `because` plusComm k m
        =~= n

-- | Natural subtraction, truncated to zero if m > n.
type n -. m = Subt n m (m <=? n)

type family Subt n m (b :: Bool) where
  Subt n m 'True = n - m
  Subt n m 'False = 0

infixl 6 -.

(%-.) :: SNat n -> SNat m -> SNat (n -. m)
n %-. m =
  case m %<=? n of
    STrue -> n %- m
    SFalse -> sZero

minPlusTruncMinus ::
  SNat n ->
  SNat m ->
  Min n m + (n -. m) :~: n
minPlusTruncMinus n m =
  case m %<=? n of
    STrue ->
      start (sMin n m %+ (n %-. m))
        === m %+ (n %-. m) `because` plusCongL (geqToMin n m Witness) (n %-. m)
        =~= m %+ (n %- m)
        === (n %- m) %+ m `because` plusComm m (n %- m)
        === n `because` minusPlus n m Witness
    SFalse ->
      start (sMin n m %+ (n %-. m))
        =~= sMin n m %+ sZero
        === sMin n m `because` plusZeroR (sMin n m)
        === n `because` leqToMin n m (notLeqToLeq m n)

truncMinusLeq :: SNat n -> SNat m -> IsTrue ((n -. m) <=? n)
truncMinusLeq n m =
  case m %<=? n of
    STrue -> leqStep (n %-. m) n m $ minusPlus n m Witness
    SFalse -> leqZero n
