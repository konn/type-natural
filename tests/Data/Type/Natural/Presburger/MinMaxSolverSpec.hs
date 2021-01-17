{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Type.Natural.Presburger.MinMaxSolverSpec where

import Control.Exception
import Control.Monad
import Data.Type.Equality
import Data.Type.Natural
import Data.Type.Natural.Presburger.Cases
import Shared
import Test.QuickCheck (ioProperty)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Unsafe.Coerce (unsafeCoerce)

test_MinMaxSolver :: TestTree
test_MinMaxSolver =
  testGroup
    "Data.Type.Natural.Presburger.MinMaxSolver"
    [ testProperty @(SomeLeq -> Property) "rejects errornousInputs" $ \case
        (SomeLeq n m) -> ioProperty @Bool $ do
          eith <- try @TypeError $ void $ evaluate $ falsity n m
          case eith of
            Left {} -> pure True
            Right {} -> pure False
    , testProperty @(SomeLeq -> Property) "minFlip" $ \case
        (SomeLeq n m) -> ioProperty @Bool $ do
          eith <- try @TypeError $ void $ evaluate $ minFlip n m
          case eith of
            Left {} -> pure False
            Right {} -> pure True
    , testProperty @(SomeLeq -> Property) "maxFlip" $ \case
        (SomeLeq n m) -> ioProperty @Bool $ do
          eith <- try @TypeError $ void $ evaluate $ maxFlip n m
          case eith of
            Left {} -> pure False
            Right {} -> pure True
    , testProperty @(SomeLeq -> Property) "maxComm" $ \case
        (SomeLeq n m) -> ioProperty @Bool $ do
          eith <- try @TypeError $ void $ evaluate $ maxComm n m
          case eith of
            Left {} -> pure False
            Right {} -> pure True
    , testProperty @(SomeLeq -> Property) "minComm" $ \case
        (SomeLeq n m) -> ioProperty @Bool $ do
          eith <- try @TypeError $ void $ evaluate $ minComm n m
          case eith of
            Left {} -> pure False
            Right {} -> pure True
    ]

data SomeLeq where
  SomeLeq :: n <= m => SNat n -> SNat m -> SomeLeq

deriving instance Show SomeLeq

instance Arbitrary SomeLeq where
  arbitrary = do
    n <- arbitrary
    dn <- arbitrary
    withSNat n $
      withSNat (n + dn) $ \(sn :: SNat n) (sm :: SNat m) ->
        gcastWith (unsafeCoerce (Refl @()) :: (n <=? m) :~: 'True) $
          pure (SomeLeq sn sm)
