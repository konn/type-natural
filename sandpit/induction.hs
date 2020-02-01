{-# LANGUAGE DataKinds, GADTs, RankNTypes, TemplateHaskell #-}
module Main where
import Data.Type.Natural
import Proof.Induction

genInduction ''Nat "inductNat"
