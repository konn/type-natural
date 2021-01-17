{-# LANGUAGE DataKinds #-}
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

    -- * Lemmas
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
    withRefl,
    (===),
    (=~=),
  )
import Proof.Propositional (IsTrue (..), eliminate, withWitness)

--------------------------------------------------

-- ** Type-level predicate & judgements.

--------------------------------------------------

-- | Comparison via GADTs.
data Leq n m where
  ZeroLeq :: SNat m -> Leq 0 m
  SuccLeqSucc :: Leq n m -> Leq (n + 1) (m + 1)

type LeqWitness n m = IsTrue (n <=? m)

data a :<: b where
  ZeroLtSucc :: 0 :<: (m + 1)
  SuccLtSucc :: n :<: m -> (n + 1) :<: (m + 1)

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
propToBoolLt ZeroLtSucc = Witness
propToBoolLt (SuccLtSucc lt) =
  withWitness (propToBoolLt lt) Witness

boolToPropLt :: n < m => SNat n -> SNat m -> n :<: m
boolToPropLt Zero (Succ _) = ZeroLtSucc
boolToPropLt (Succ _) Zero = eliminate (Refl :: 0 :~: 1)
boolToPropLt (Succ n) (Succ m) = SuccLtSucc (boolToPropLt n m)

type Min n m = MinAux (n <=? m) n m

sMin :: SNat n -> SNat m -> SNat (Min n m)
sMin = coerce $ min @Natural

sMax :: SNat n -> SNat m -> SNat (Max n m)
sMax = coerce $ max @Natural

type family MinAux (p :: Bool) (n :: Nat) (m :: Nat) :: Nat where
  MinAux 'True n _ = n
  MinAux 'False _ m = m

type Max n m = MaxAux (n >=? m) n m

type family MaxAux (p :: Bool) (n :: Nat) (m :: Nat) :: Nat where
  MaxAux 'True n _ = n
  MaxAux 'False _ m = m

infix 4 <?, <, >=?, >=, >, >?

type n <? m = n + 1 <=? m

(%<?) :: SNat n -> SNat m -> SBool (n <? m)
(%<?) = (%<=?) . sSucc

type n < m = (n <? m) ~ 'True

type n >=? m = m <=? n

(%>=?) :: SNat n -> SNat m -> SBool (n >=? m)
(%>=?) = flip (%<=?)

type n >= m = (n >=? m) ~ 'True

type n >? m = m <? n

(%>?) :: SNat n -> SNat m -> SBool (n >? m)
(%>?) = flip (%<?)

type n > m = (n >? m) ~ 'True

infix 4 %>?, %<?, %>=?

data LeqView n m where
  LeqZero :: SNat n -> LeqView 0 n
  LeqSucc :: SNat n -> SNat m -> IsTrue (n <=? m) -> LeqView (Succ n) (Succ m)

data DiffNat n m where
  DiffNat :: SNat n -> SNat m -> DiffNat n (n + m)

newtype LeqWitPf n = LeqWitPf {leqWitPf :: forall m. SNat m -> IsTrue (n <=? m) -> DiffNat n m}

newtype LeqStepPf n = LeqStepPf {leqStepPf :: forall m l. SNat m -> SNat l -> n + l :~: m -> IsTrue (n <=? m)}

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

newtype LTSucc n = LTSucc {proofLTSucc :: CmpNat n (Succ n) :~: 'LT}

newtype CmpSuccStepR n = CmpSuccStepR
  { proofCmpSuccStepR ::
      forall m.
      SNat m ->
      CmpNat n m :~: 'LT ->
      CmpNat n (Succ m) :~: 'LT
  }

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
succLeqToLT a b saLEQb =
  case leqWitness (sSucc a) b saLEQb of
    DiffNat _ k ->
      let aLEQb =
            leqStep a b (sSucc k) $
              start (a %+ sSucc k)
                === sSucc (a %+ k) `because` plusSuccR a k
                === sSucc a %+ k `because` sym (plusSuccL a k)
                =~= b
          aNEQb aeqb =
            succNonCyclic k $
              plusEqCancelL a (sSucc k) sZero $
                start (a %+ sSucc k)
                  === sSucc (a %+ k) `because` plusSuccR a k
                  === sSucc a %+ k `because` sym (plusSuccL a k)
                  =~= b
                  === a `because` sym aeqb
                  === a %+ sZero `because` sym (plusZeroR a)
       in leqNeqToLT a b aLEQb aNEQb

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
gtToLeq n m nGTm =
  ltToLeq m n $
    start (sCmpNat m n) === sFlipOrdering (sCmpNat n m) `because` sym (flipCmpNat n m)
      === sFlipOrdering SGT `because` congFlipOrdering nGTm
      =~= SLT

congFlipOrdering ::
  a :~: b -> FlipOrdering a :~: FlipOrdering b
congFlipOrdering Refl = Refl

ltToSuccLeq ::
  SNat a ->
  SNat b ->
  CmpNat a b :~: 'LT ->
  IsTrue (Succ a <=? b)
ltToSuccLeq n m nLTm =
  leqNeqToSuccLeq n m (ltToLeq n m nLTm) (ltToNeq n m nLTm)

cmpZero :: SNat a -> CmpNat 0 (Succ a) :~: 'LT
cmpZero sn =
  leqToLT sZero (sSucc sn) $
    leqStep (sSucc sZero) (sSucc sn) sn $
      start (sSucc sZero %+ sn)
        === sSucc (sZero %+ sn) `because` plusSuccL sZero sn
        === sSucc sn `because` succCong (plusZeroL sn)

leqToGT ::
  SNat a ->
  SNat b ->
  IsTrue (Succ b <=? a) ->
  CmpNat a b :~: 'GT
leqToGT a b sbLEQa =
  start (sCmpNat a b)
    === sFlipOrdering (sCmpNat b a) `because` sym (flipCmpNat b a)
    === sFlipOrdering SLT `because` congFlipOrdering (leqToLT b a sbLEQa)
    =~= SGT

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
ltRightPredSucc a b aLTb =
  case zeroOrSucc b of
    IsZero -> absurd $ zeroNoLT a aLTb
    IsSucc b' ->
      sym $
        start (sSucc (sPred b))
          =~= sSucc (sPred (sSucc b'))
          === sSucc b' `because` succCong (predSucc b')
          =~= b

cmpSucc :: SNat n -> SNat m -> CmpNat n m :~: CmpNat (Succ n) (Succ m)
cmpSucc n m =
  case sCmpNat n m of
    SEQ ->
      let nEQm = eqToRefl n m Refl
       in sym $ eqlCmpEQ (sSucc n) (sSucc m) $ succCong nEQm
    SLT -> case leqWitness (sSucc n) m $ ltToSuccLeq n m Refl of
      DiffNat _ k ->
        sym $
          succLeqToLT (sSucc n) (sSucc m) $
            leqStep (sSucc (sSucc n)) (sSucc m) k $
              start (sSucc (sSucc n) %+ k)
                === sSucc (sSucc n %+ k) `because` plusSuccL (sSucc n) k
                =~= sSucc m
    SGT -> case leqWitness (sSucc m) n $ ltToSuccLeq m n (sym $ flipCmpNat n m) of
      DiffNat _ k ->
        let pf =
              ( succLeqToLT (sSucc m) (sSucc n) $
                  leqStep (sSucc (sSucc m)) (sSucc n) k $
                    start (sSucc (sSucc m) %+ k)
                      === sSucc (sSucc m %+ k) `because` plusSuccL (sSucc m) k
                      =~= sSucc n
              )
         in start (sCmpNat n m)
              =~= SGT
              =~= sFlipOrdering SLT
              === sFlipOrdering (sCmpNat (sSucc m) (sSucc n)) `because` congFlipOrdering (sym pf)
              === sCmpNat (sSucc n) (sSucc m) `because` flipCmpNat (sSucc m) (sSucc n)

ltSucc :: SNat a -> CmpNat a (Succ a) :~: 'LT
ltSucc = proofLTSucc . induction base step
  where
    base :: LTSucc 0
    base = LTSucc $ cmpZero (sZero :: SNat 0)

    step :: SNat n -> LTSucc n -> LTSucc (Succ n)
    step n (LTSucc ih) =
      LTSucc $
        start (sCmpNat (sSucc n) (sSucc (sSucc n)))
          === sCmpNat n (sSucc n) `because` sym (cmpSucc n (sSucc n))
          === SLT `because` ih

cmpSuccStepR ::
  SNat n ->
  SNat m ->
  CmpNat n m :~: 'LT ->
  CmpNat n (Succ m) :~: 'LT
cmpSuccStepR = proofCmpSuccStepR . induction base step
  where
    base :: CmpSuccStepR 0
    base = CmpSuccStepR $ \m _ -> cmpZero m

    step :: SNat n -> CmpSuccStepR n -> CmpSuccStepR (Succ n)
    step n (CmpSuccStepR ih) = CmpSuccStepR $ \m snltm ->
      case zeroOrSucc m of
        IsZero -> absurd $ zeroNoLT (sSucc n) snltm
        IsSucc m' ->
          let nLTm' = trans (cmpSucc n m') snltm
           in start (sCmpNat (sSucc n) (sSucc m))
                =~= sCmpNat (sSucc n) (sSucc (sSucc m'))
                === sCmpNat n (sSucc m') `because` sym (cmpSucc n (sSucc m'))
                === SLT `because` ih m' nLTm'

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
leqToLT n m snLEQm =
  case leqToCmp (sSucc n) m snLEQm of
    Left eql ->
      withRefl eql $
        start (sCmpNat n m)
          =~= sCmpNat n (sSucc n)
          === SLT `because` ltSucc n
    Right nLTm -> ltSuccLToLT n m nLTm

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

leqWitness :: SNat n -> SNat m -> IsTrue (n <=? m) -> DiffNat n m
leqWitness = leqWitPf . induction base step
  where
    base :: LeqWitPf 0
    base = LeqWitPf $ \sm _ -> gcastWith (plusZeroL sm) $ DiffNat sZero sm

    step :: SNat n -> LeqWitPf n -> LeqWitPf (Succ n)
    step (n :: SNat n) (LeqWitPf ih) = LeqWitPf $ \m snLEQm ->
      case viewLeq (sSucc n) m snLEQm of
        LeqZero _ -> absurd $ succNonCyclic n Refl
        LeqSucc (_ :: SNat n') pm nLEQpm ->
          succDiffNat n pm $ ih pm $ coerceLeqL (succInj Refl :: n' :~: n) pm nLEQpm

leqStep :: SNat n -> SNat m -> SNat l -> n + l :~: m -> IsTrue (n <=? m)
leqStep = leqStepPf . induction base step
  where
    base :: LeqStepPf 0
    base = LeqStepPf $ \k _ _ -> leqZero k

    step :: SNat n -> LeqStepPf n -> LeqStepPf (Succ n)
    step n (LeqStepPf ih) =
      LeqStepPf $ \k l snPlEqk ->
        let kEQspk =
              start k
                === sSucc n %+ l `because` sym snPlEqk
                === sSucc (n %+ l) `because` plusSuccL n l
            pk = n %+ l
         in coerceLeqR (sSucc n) (sym kEQspk) $ leqSucc n pk $ ih pk l Refl

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
leqRefl sn = leqStep sn sn sZero (plusZeroR sn)

leqSuccStepR :: SNat n -> SNat m -> IsTrue (n <=? m) -> IsTrue (n <=? Succ m)
leqSuccStepR n m nLEQm =
  case leqWitness n m nLEQm of
    DiffNat _ k ->
      leqStep n (sSucc m) (sSucc k) $
        start (n %+ sSucc k) === sSucc (n %+ k) `because` plusSuccR n k =~= sSucc m

leqSuccStepL :: SNat n -> SNat m -> IsTrue (Succ n <=? m) -> IsTrue (n <=? m)
leqSuccStepL n m snLEQm =
  leqTrans n (sSucc n) m (leqSuccStepR n n $ leqRefl n) snLEQm

leqReflexive :: SNat n -> SNat m -> n :~: m -> IsTrue (n <=? m)
leqReflexive n _ Refl = leqRefl n

leqTrans :: SNat n -> SNat m -> SNat l -> IsTrue (n <=? m) -> IsTrue (m <=? l) -> IsTrue (n <=? l)
leqTrans n m k nLEm mLEk =
  case leqWitness n m nLEm of
    DiffNat _ mMn -> case leqWitness m k mLEk of
      DiffNat _ kMn -> leqStep n k (mMn %+ kMn) (sym $ plusAssoc n mMn kMn)

leqAntisymm :: SNat n -> SNat m -> IsTrue (n <=? m) -> IsTrue (m <=? n) -> n :~: m
leqAntisymm n m nLEm mLEn =
  case (leqWitness n m nLEm, leqWitness m n mLEn) of
    (DiffNat _ mMn, DiffNat _ nMm) ->
      let pEQ0 =
            plusEqCancelL n (mMn %+ nMm) sZero $
              start (n %+ (mMn %+ nMm))
                === (n %+ mMn) %+ nMm
                  `because` sym (plusAssoc n mMn nMm)
                =~= m %+ nMm
                =~= n
                === n %+ sZero
                  `because` sym (plusZeroR n)
          nMmEQ0 = plusEqZeroL mMn nMm pEQ0
       in sym $
            start m
              =~= n %+ mMn
              === n %+ sZero `because` plusCongR n nMmEQ0
              === n `because` plusZeroR n

plusMonotone ::
  SNat n ->
  SNat m ->
  SNat l ->
  SNat k ->
  IsTrue (n <=? m) ->
  IsTrue (l <=? k) ->
  IsTrue ((n + l) <=? (m + k))
plusMonotone n m l k nLEm lLEk =
  case (leqWitness n m nLEm, leqWitness l k lLEk) of
    (DiffNat _ mMINn, DiffNat _ kMINl) ->
      let r = mMINn %+ kMINl
       in leqStep (n %+ l) (m %+ k) r $
            start (n %+ l %+ r)
              === n %+ (l %+ r)
                `because` plusAssoc n l r
              =~= n %+ (l %+ (mMINn %+ kMINl))
              === n %+ (l %+ (kMINl %+ mMINn))
                `because` plusCongR n (plusCongR l (plusComm mMINn kMINl))
              === n %+ ((l %+ kMINl) %+ mMINn)
                `because` plusCongR n (sym $ plusAssoc l kMINl mMINn)
              =~= n %+ (k %+ mMINn)
              === n %+ (mMINn %+ k)
                `because` plusCongR n (plusComm k mMINn)
              === n %+ mMINn %+ k
                `because` sym (plusAssoc n mMINn k)
              =~= m %+ k

leqZeroElim :: SNat n -> IsTrue (n <=? 0) -> n :~: 0
leqZeroElim n nLE0 =
  case viewLeq n sZero nLE0 of
    LeqZero _ -> Refl
    LeqSucc _ pZ _ -> absurd $ succNonCyclic pZ Refl

plusMonotoneL ::
  SNat n ->
  SNat m ->
  SNat l ->
  IsTrue (n <=? m) ->
  IsTrue ((n + l) <=? (m + l))
plusMonotoneL n m l leq = plusMonotone n m l l leq (leqRefl l)

plusMonotoneR ::
  SNat n ->
  SNat m ->
  SNat l ->
  IsTrue (m <=? l) ->
  IsTrue ((n + m) <=? (n + l))
plusMonotoneR n m l leq = plusMonotone n n m l (leqRefl n) leq

plusLeqL :: SNat n -> SNat m -> IsTrue (n <=? (n + m))
plusLeqL n m = leqStep n (n %+ m) m Refl

plusLeqR :: SNat n -> SNat m -> IsTrue (m <=? (n + m))
plusLeqR n m = leqStep m (n %+ m) n $ plusComm m n

plusCancelLeqR ::
  SNat n ->
  SNat m ->
  SNat l ->
  IsTrue ((n + l) <=? (m + l)) ->
  IsTrue (n <=? m)
plusCancelLeqR n m l nlLEQml =
  case leqWitness (n %+ l) (m %+ l) nlLEQml of
    DiffNat _ k ->
      let pf =
            plusEqCancelR (n %+ k) m l $
              start ((n %+ k) %+ l)
                === n %+ (k %+ l) `because` plusAssoc n k l
                === n %+ (l %+ k) `because` plusCongR n (plusComm k l)
                === n %+ l %+ k `because` sym (plusAssoc n l k)
                =~= m %+ l
       in leqStep n m k pf

plusCancelLeqL ::
  SNat n ->
  SNat m ->
  SNat l ->
  IsTrue ((n + m) <=? (n + l)) ->
  IsTrue (m <=? l)
plusCancelLeqL n m l nmLEQnl =
  plusCancelLeqR m l n $
    coerceLeqL (plusComm n m) (l %+ n) $
      coerceLeqR (n %+ m) (plusComm n l) nmLEQnl

succLeqZeroAbsurd :: SNat n -> IsTrue (S n <=? 0) -> Void
succLeqZeroAbsurd n leq =
  succNonCyclic n (leqZeroElim (sSucc n) leq)

succLeqZeroAbsurd' :: SNat n -> (S n <=? 0) :~: 'False
succLeqZeroAbsurd' n =
  case sSucc n %<=? sZero of
    STrue -> absurd $ succLeqZeroAbsurd n Witness
    SFalse -> Refl

succLeqAbsurd :: SNat n -> IsTrue (S n <=? n) -> Void
succLeqAbsurd n snLEQn =
  eliminate $
    start SLT
      === sCmpNat n n `because` sym (succLeqToLT n n snLEQn)
      === SEQ `because` eqlCmpEQ n n Refl

succLeqAbsurd' :: SNat n -> (S n <=? n) :~: 'False
succLeqAbsurd' n =
  case sSucc n %<=? n of
    STrue -> absurd $ succLeqAbsurd n Witness
    SFalse -> Refl

notLeqToLeq :: ((n <=? m) ~ 'False) => SNat n -> SNat m -> IsTrue (m <=? n)
notLeqToLeq n m =
  case sCmpNat n m of
    SLT -> eliminate $ ltToLeq n m Refl
    SEQ -> eliminate $ leqReflexive n m $ eqToRefl n m Refl
    SGT -> gtToLeq n m Refl

leqSucc' :: SNat n -> SNat m -> (n <=? m) :~: (Succ n <=? Succ m)
leqSucc' _ _ = Refl

leqToMin :: SNat n -> SNat m -> IsTrue (n <=? m) -> Min n m :~: n
leqToMin _ _ Witness = Refl

geqToMin :: SNat n -> SNat m -> IsTrue (m <=? n) -> Min n m :~: m
geqToMin n m Witness =
  case n %<=? m of
    SFalse -> Refl
    STrue -> Refl

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
minLargest l n m lLEQn lLEQm =
  withKnownNat l $
    withKnownNat n $
      withKnownNat m $
        withKnownNat (sMin n m) $
          case n %<=? m of
            STrue -> lLEQn
            SFalse -> lLEQm

leqToMax :: SNat n -> SNat m -> IsTrue (n <=? m) -> Max n m :~: m
leqToMax n m nLEQm =
  leqAntisymm (sMax n m) m (maxLeast m n m nLEQm (leqRefl m)) (maxLeqR n m)

geqToMax :: SNat n -> SNat m -> IsTrue (m <=? n) -> Max n m :~: n
geqToMax n m mLEQn =
  leqAntisymm (sMax n m) n (maxLeast n n m (leqRefl n) mLEQn) (maxLeqL n m)

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
maxLeast l n m lLEQn lLEQm =
  withKnownNat l $
    withKnownNat n $
      withKnownNat m $
        withKnownNat (sMax n m) $
          case n %>=? m of
            STrue -> lLEQn
            SFalse -> lLEQm

lneqSuccLeq :: SNat n -> SNat m -> (n < m) :~: (Succ n <= m)
lneqSuccLeq _ _ = Refl

lneqReversed :: SNat n -> SNat m -> (n < m) :~: (m > n)
lneqReversed _ _ = Refl

lneqToLT ::
  SNat n ->
  SNat m ->
  IsTrue (n <? m) ->
  CmpNat n m :~: 'LT
lneqToLT n m nLNEm =
  succLeqToLT n m $ gcastWith (lneqSuccLeq n m) nLNEm

ltToLneq ::
  SNat n ->
  SNat m ->
  CmpNat n m :~: 'LT ->
  IsTrue (n <? m)
ltToLneq n m nLTm =
  gcastWith (sym $ lneqSuccLeq n m) $ ltToSuccLeq n m nLTm

lneqZero :: SNat a -> IsTrue (0 <? Succ a)
lneqZero n = ltToLneq sZero (sSucc n) $ cmpZero n

lneqSucc :: SNat n -> IsTrue (n <? Succ n)
lneqSucc n = ltToLneq n (sSucc n) $ ltSucc n

succLneqSucc ::
  SNat n ->
  SNat m ->
  (n <? m) :~: (Succ n <? Succ m)
succLneqSucc _ _ = Refl

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
