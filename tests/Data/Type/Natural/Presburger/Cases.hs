{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fplugin Data.Type.Natural.Presburger.MinMaxSolver #-}

module Data.Type.Natural.Presburger.Cases where

import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality
import Data.Type.Natural
import GHC.TypeNats

minFlip :: n <= m => p n -> q m -> Min m n :~: n
minFlip _ _ = Refl

maxFlip :: n <= m => p n -> q m -> Max m n :~: m
maxFlip _ _ = Refl

minComm :: q m -> p n -> Min n m :~: Min m n
minComm _ _ = Refl

maxComm :: q m -> p n -> Max n m :~: Max m n
maxComm _ _ = Refl

falsity :: n <= m => p n -> q m -> Min n m :~: m
falsity _ _  = Refl
