{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Type.Natural.Lemma.OrderSpec where

import Data.Type.Equality ((:~:) (Refl))
import Data.Type.Natural
import Data.Type.Natural.Lemma.Order
import Proof.Propositional (IsTrue (Witness))
import Shared ()
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck
import Unsafe.Coerce (unsafeCoerce)

someNat' :: NonNegative Integer -> SomeSNat
someNat' = toSomeSNat . fromInteger . getNonNegative

data SomeLeqNat where
  MkSomeLeqNat :: n <= m => SNat n -> SNat m -> SomeLeqNat

deriving instance Show SomeLeqNat

instance Arbitrary SomeLeqNat where
  arbitrary = do
    SomeSNat n <- someNat' <$> arbitrary
    SomeSNat m <- someNat' <$> arbitrary
    case n %<=? m of
      STrue -> pure $ MkSomeLeqNat n m
      SFalse ->
        case m %<=? n of
          STrue -> pure $ MkSomeLeqNat m n
          SFalse -> error "Impossible!"

test_Lemmas :: TestTree
test_Lemmas =
  testGroup
    "Lemmas"
    [ testProperty @(SomeLeqNat -> Property) "coerceLeqL terminates" $ \(MkSomeLeqNat (_ :: SNat n) sm) -> coerceLeqL (Refl :: n :~: n) sm Witness === Witness
    , testProperty @(SomeLeqNat -> Property) "coerceLeqR terminates" $ \(MkSomeLeqNat sn (_ :: SNat m)) -> coerceLeqR sn (Refl :: m :~: m) Witness === Witness
    , testProperty @(SomeSNat -> SomeSNat -> Property) "sLeqCong terminates" $
        \(SomeSNat (_ :: SNat n)) (SomeSNat (_ :: SNat m)) ->
          sLeqCong (Refl @n) (Refl @m) === Refl
    , testProperty @(SomeSNat -> SomeSNat -> Property) "succDiffNat terminates and gives the correct value" $
        \(SomeSNat sn) (SomeSNat sm) ->
          case succDiffNat sn (sn %+ sm) (DiffNat sn sm) of
            DiffNat sns sms ->
              toNatural (sns %+ sms)
                === toNatural sn + toNatural sm + 1
    , testProperty @(SomeSNat -> SomeSNat -> Property)
        "compareCongR terminates"
        $ \(SomeSNat a) (SomeSNat (_ :: SNat b)) ->
          compareCongR a (Refl @b) === Refl
    , testProperty @(SomeLeqNat -> Property)
        "leqToCmp works properly"
        $ \case
          MkSomeLeqNat a b ->
            case leqToCmp a b Witness of
              Left Refl -> toNatural a === toNatural b
              Right Refl ->
                property $ toNatural a < toNatural b
    , testProperty @(SomeSNat -> Property)
        "eqlCmpEQ terminates"
        $ \(SomeSNat n) ->
          case eqlCmpEQ n n Refl of
            Refl -> property True
    , testProperty @(SomeSNat -> Property)
        "eqToRefl terminates"
        $ \(SomeSNat n) ->
          case eqToRefl n n Refl of
            Refl -> property True
    , testProperty @(SomeSNat -> SomeSNat -> Property)
        "flipCmpNat terminates"
        $ \(SomeSNat n) (SomeSNat m) ->
          case flipCmpNat n m of
            Refl -> property True
    , testProperty @(SomeSNat -> Property)
        "ltToNeq terminates"
        $ \(SomeSNat n) ->
          expectFailure $
            total $
              ltToNeq n n (unsafeCoerce $ Refl @()) Refl
    , testProperty @(SomeLeqNat -> Property)
        "leqNeqToLT terminates"
        $ \(MkSomeLeqNat n m) ->
          case n %~ m of
            Equal -> discard
            NonEqual ->
              case leqNeqToLT n m Witness (\case {}) of
                Refl -> property True
    ]
