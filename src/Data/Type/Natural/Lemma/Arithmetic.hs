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
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Data.Type.Natural.Lemma.Arithmetic
  ( Zero,
    One,
    S,
    sZero,
    sOne,
    ZeroOrSucc (..),
    plusCong,
    plusCongR,
    plusCongL,
    predCong,
    Succ,
    sS,
    sSucc,
    Pred,
    sPred,
    sPred',
    succCong,
    multCong,
    multCongL,
    multCongR,
    minusCong,
    minusCongL,
    minusCongR,
    succOneCong,
    succInj,
    succInj',
    succNonCyclic,
    induction,
    plusMinus,
    plusMinus',
    plusZeroL,
    plusSuccL,
    plusZeroR,
    plusSuccR,
    plusComm,
    plusAssoc,
    multZeroL,
    multSuccL,
    multSuccL',
    multZeroR,
    multSuccR,
    multComm,
    multOneR,
    multOneL,
    plusMultDistrib,
    multPlusDistrib,
    minusNilpotent,
    multAssoc,
    plusEqCancelL,
    plusEqCancelR,
    succAndPlusOneL,
    succAndPlusOneR,
    predSucc,
    viewNat,
    zeroOrSucc,
    plusEqZeroL,
    plusEqZeroR,
    predUnique,
    multEqSuccElimL,
    multEqSuccElimR,
    minusZero,
    multEqCancelR,
    succPred,
    multEqCancelL,
    pattern Zero,
    pattern Succ,
  )
where

import Data.Type.Equality
  ( gcastWith,
    (:~:) (..),
  )
import Data.Type.Natural.Core
import Data.Type.Natural.Lemma.Presburger
  ( plusEqZeroL,
    plusEqZeroR,
    succNonCyclic,
  )
import Data.Void (Void, absurd)
import Proof.Equational (because, start, sym, trans, (===))

predCong :: n :~: m -> Pred n :~: Pred m
predCong Refl = Refl

plusCong :: n :~: m -> n' :~: m' -> n + n' :~: m + m'
plusCong Refl Refl = Refl

plusCongL :: n :~: m -> SNat k -> n + k :~: m + k
plusCongL Refl _ = Refl

plusCongR :: SNat k -> n :~: m -> k + n :~: k + m
plusCongR _ Refl = Refl

succCong :: n :~: m -> S n :~: S m
succCong Refl = Refl

multCong :: n :~: m -> l :~: k -> n * l :~: m * k
multCong Refl Refl = Refl

multCongL :: n :~: m -> SNat k -> n * k :~: m * k
multCongL Refl _ = Refl

multCongR :: SNat k -> n :~: m -> k * n :~: k * m
multCongR _ Refl = Refl

minusCong :: n :~: m -> l :~: k -> n - l :~: m - k
minusCong Refl Refl = Refl

minusCongL :: n :~: m -> SNat k -> n - k :~: m - k
minusCongL Refl _ = Refl

minusCongR :: SNat k -> n :~: m -> k - n :~: k - m
minusCongR _ Refl = Refl

succOneCong :: Succ 0 :~: 1
succOneCong = Refl

succInj :: Succ n :~: Succ m -> n :~: m
succInj Refl = Refl

succInj' :: proxy n -> proxy' m -> Succ n :~: Succ m -> n :~: m
succInj' _ _ = succInj

induction :: forall p k. p 0 -> (forall n. SNat n -> p n -> p (S n)) -> SNat k -> p k
induction base step = go
  where
    go :: SNat m -> p m
    go sn = case viewNat sn of
      IsZero -> base
      IsSucc n -> withKnownNat n $ step n (go n)

plusMinus :: SNat n -> SNat m -> n + m - m :~: n
plusMinus _ _ = Refl

plusMinus' :: SNat n -> SNat m -> n + m - n :~: m
plusMinus' n m =
  start (n %+ m %- n)
    === m %+ n %- n `because` minusCongL (plusComm n m) n
    === m `because` plusMinus m n

plusZeroL :: SNat n -> (0 + n) :~: n
plusZeroL _ = Refl

plusSuccL :: SNat n -> SNat m -> S n + m :~: S (n + m)
plusSuccL _ _ = Refl

plusZeroR :: SNat n -> (n + 0) :~: n
plusZeroR _ = Refl

plusSuccR :: SNat n -> SNat m -> n + S m :~: S (n + m)
plusSuccR _ _ = Refl

plusComm :: SNat n -> SNat m -> n + m :~: m + n
plusComm _ _ = Refl

plusAssoc ::
  forall n m l.
  SNat n ->
  SNat m ->
  SNat l ->
  (n + m) + l :~: n + (m + l)
plusAssoc _ _ _ = Refl

multZeroL :: SNat n -> 0 * n :~: 0
multZeroL _ = Refl

multSuccL :: SNat n -> SNat m -> S n * m :~: n * m + m
multSuccL _ _ = Refl

multSuccL' :: SNat n -> SNat m -> S n * m :~: n * m + 1 * m
multSuccL' _ _ = Refl

multZeroR :: SNat n -> n * 0 :~: 0
multZeroR _ = Refl

multSuccR :: SNat n -> SNat m -> n * S m :~: n * m + n
multSuccR _ _ = Refl

multComm :: SNat n -> SNat m -> n * m :~: m * n
multComm _ _ = Refl

multOneR :: SNat n -> n * 1 :~: n
multOneR _ = Refl

multOneL :: SNat n -> 1 * n :~: n
multOneL _ = Refl

plusMultDistrib ::
  SNat n ->
  SNat m ->
  SNat l ->
  (n + m) * l :~: (n * l) + (m * l)
plusMultDistrib _ _ _ = Refl

multPlusDistrib ::
  SNat n ->
  SNat m ->
  SNat l ->
  n * (m + l) :~: (n * m) + (n * l)
multPlusDistrib _ _ _ = Refl

minusNilpotent :: SNat n -> n - n :~: 0
minusNilpotent _ = Refl

multAssoc ::
  SNat n ->
  SNat m ->
  SNat l ->
  (n * m) * l :~: n * (m * l)
multAssoc _ _ _ = Refl

plusEqCancelL :: SNat n -> SNat m -> SNat l -> n + m :~: n + l -> m :~: l
plusEqCancelL _ _ _ Refl = Refl

plusEqCancelR :: forall n m l. SNat n -> SNat m -> SNat l -> n + l :~: m + l -> n :~: m
plusEqCancelR n m l nlml =
  plusEqCancelL l n m $
    start (l %+ n)
      === (n %+ l) `because` plusComm l n
      === (m %+ l) `because` nlml
      === (l %+ m) `because` plusComm m l

succAndPlusOneL :: SNat n -> Succ n :~: 1 + n
succAndPlusOneL _ = Refl

succAndPlusOneR :: SNat n -> Succ n :~: n + 1
succAndPlusOneR _ = Refl

predSucc :: SNat n -> Pred (Succ n) :~: n
predSucc _ = Refl

zeroOrSucc :: SNat n -> ZeroOrSucc n
zeroOrSucc = viewNat

predUnique :: SNat n -> SNat m -> Succ n :~: m -> n :~: Pred m
predUnique _ _ Refl = Refl

minusZero :: SNat n -> n - 0 :~: n
minusZero _ = Refl

multEqCancelR :: forall n m l. SNat n -> SNat m -> SNat l -> n * Succ l :~: m * Succ l -> n :~: m
multEqCancelR _ _ = go
  where
    go :: forall k. SNat k -> n * Succ k :~: m * Succ k -> n :~: m
    go Zero Refl = Refl
    go (Succ n) Refl = gcastWith (go n Refl) Refl

succPred :: SNat n -> (n :~: 0 -> Void) -> Succ (Pred n) :~: n
succPred n nonZero =
  case zeroOrSucc n of
    IsZero -> absurd $ nonZero Refl
    IsSucc n' -> sym $ succCong $ predUnique n' n Refl

multEqCancelL :: SNat n -> SNat m -> SNat l -> Succ n * m :~: Succ n * l -> m :~: l
multEqCancelL n m l snmEsnl =
  multEqCancelR m l n $
    multComm m (sSucc n) `trans` snmEsnl `trans` multComm (sSucc n) l

sPred' :: proxy n -> SNat (Succ n) -> SNat n
sPred' pxy sn = gcastWith (succInj $ succCong $ predSucc (sPred' pxy sn)) (sPred sn)

multEqSuccElimL ::
  SNat n ->
  SNat m ->
  SNat l ->
  n * m :~: Succ l ->
  n :~: Succ (Pred n)
multEqSuccElimL Zero _ l Refl = absurd $ succNonCyclic l Refl
multEqSuccElimL (Succ _) _ _ Refl = Refl

multEqSuccElimR :: SNat n -> SNat m -> SNat l -> n * m :~: Succ l -> m :~: Succ (Pred m)
multEqSuccElimR _ Zero l Refl = absurd $ succNonCyclic l Refl
multEqSuccElimR _ (Succ _) _ Refl = Refl
