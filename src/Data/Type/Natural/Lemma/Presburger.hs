{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}

module Data.Type.Natural.Lemma.Presburger where

import Data.Type.Equality
import Data.Type.Natural.Core
import Data.Void

plusEqZeroL :: SNat n -> SNat m -> n + m :~: 0 -> n :~: 0
plusEqZeroL _ _ Refl = Refl

plusEqZeroR :: SNat n -> SNat m -> n + m :~: 0 -> m :~: 0
plusEqZeroR _ _ Refl = Refl

succNonCyclic :: SNat n -> Succ n :~: 0 -> Void
succNonCyclic Zero r = case r of
succNonCyclic (Succ n) Refl = succNonCyclic n Refl
