{-# LANGUAGE DataKinds, KindSignatures, TypeFamilies, TypeFamilyDependencies #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
module Main where
import GHC.TypeLits

type family S (n :: Nat) = (sn :: Nat) | sn -> n where
  S n = n + 1

main :: IO ()
main = return ()
