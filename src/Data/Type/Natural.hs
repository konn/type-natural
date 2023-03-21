{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

-- | Coercion between Peano Numerals @'Data.Type.Natural.Nat'@ and builtin naturals @'GHC.TypeLits.Nat'@
module Data.Type.Natural
  ( -- * Type-level naturals

    -- ** @Nat@, singletons and KnownNat manipulation,
    Nat,
    KnownNat,
    SNat (Succ, Zero),
    sNat,
    sNatP,
    toNatural,
    SomeSNat (..),
    toSomeSNat,
    withSNat,
    withKnownNat,
    fromSNat,
    natVal,
    natVal',
    someNatVal,
    SomeNat (..),
    (%~),
    Equality (..),
    type (===),

    -- *** Pattens and Views
    viewNat,
    zeroOrSucc,
    ZeroOrSucc (..),

    -- ** Promtoed and singletonised operations

    -- *** Arithmetic
    Succ,
    sSucc,
    S,
    Pred,
    sPred,
    sS,
    Zero,
    sZero,
    One,
    sOne,
    type (+),
    (%+),
    type (-),
    (%-),
    type (*),
    (%*),
    Div,
    sDiv,
    Mod,
    sMod,
    type (^),
    (%^),
    type (-.),
    (%-.),
    Log2,
    sLog2,

    -- *** Ordering
    type (<=?),
    type (<=),
    (%<=?),
    type (<?),
    type (<),
    (%<?),
    type (>=?),
    type (>=),
    (%>=?),
    type (>?),
    type (>),
    (%>?),
    CmpNat,
    sCmpNat,
    sCompare,
    Min,
    sMin,
    Max,
    sMax,
    induction,

    -- * QuasiQuotes
    snat,

    -- * Singletons for auxiliary types
    SBool (..),
    SOrdering (..),
    OrderingI(..),
    fromOrderingI,
    toOrderingI,
    FlipOrdering,
    sFlipOrdering,
  )
where

import Data.Proxy (Proxy)
import Data.Type.Natural.Core
import Data.Type.Natural.Lemma.Arithmetic
import Data.Type.Natural.Lemma.Order
import Language.Haskell.TH (litT, numTyLit)
import Language.Haskell.TH.Quote
import Text.Read (readMaybe)
import Data.Ord (comparing)
import Data.Function (on)

{- | Quotesi-quoter for SNatleton types for @'GHC.TypeLits.Nat'@. This can be used for an expression.

  For example: @[snat|12|] '%+' [snat| 5 |]@.
-}
snat :: QuasiQuoter
snat =
  QuasiQuoter
    { quoteExp = \str ->
        case readMaybe str of
          Just n -> [|sNat :: SNat $(litT $ numTyLit n)|]
          Nothing -> error "Must be natural literal"
    , quotePat = \str ->
        case readMaybe str of
          Just n -> [p|((%~ (sNat :: SNat $(litT $ numTyLit n))) -> Equal)|]
          Nothing -> error "Must be natural literal"
    , quoteType = \str ->
        case readMaybe str of
          Just n -> litT $ numTyLit n
          Nothing -> error "Must be natural literal"
    , quoteDec = error "No declaration Quotes for Nat"
    }

toNatural :: SNat n -> Natural
{-# DEPRECATED toNatural "Use fromSNat instead" #-}
toNatural = fromSNat

data SomeSNat where
  SomeSNat :: KnownNat n => SNat n -> SomeSNat

deriving instance Show SomeSNat

instance Eq SomeSNat where
  (==) = (==) `on` \(SomeSNat n) -> fromSNat n
  {-# INLINE (==) #-}

instance Ord SomeSNat where
  compare = comparing (\(SomeSNat n) -> fromSNat n)
  {-# INLINE compare #-}

toSomeSNat :: Natural -> SomeSNat
toSomeSNat n = case someNatVal n of
  SomeNat pn -> withKnownNat sn $ SomeSNat sn
    where
      sn = sNatP pn

withSNat :: Natural -> (forall n. KnownNat n => SNat n -> r) -> r
withSNat n act = case someNatVal n of
  SomeNat (pn :: Proxy n) -> withKnownNat sn $ act sn
    where
      sn = sNatP pn

sNatP :: KnownNat n => pxy n -> SNat n
sNatP = const sNat
