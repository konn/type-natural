{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs      #-}
{-# LANGUAGE KindSignatures, PolyKinds, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators               #-}
{-# LANGUAGE UndecidableInstances                                       #-}
module Main where
import Data.Singletons.TH
import Data.Type.Natural

singletons [d|
 pred :: Nat -> Nat
 pred Z = Z
 pred (S n) = n
 |]
