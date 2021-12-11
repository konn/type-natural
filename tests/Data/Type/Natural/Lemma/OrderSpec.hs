{-# LANGUAGE DataKinds #-}
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

data SomeLtNat where
  MkSomeLtNat ::
    CmpNat n m ~ 'LT =>
    SNat n ->
    SNat m ->
    SomeLtNat

data SomeGtNat where
  MkSomeGtNat ::
    CmpNat n m ~ 'GT =>
    SNat n ->
    SNat m ->
    SomeGtNat

deriving instance Show SomeLeqNat

deriving instance Show SomeLtNat

deriving instance Show SomeGtNat

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

instance Arbitrary SomeLtNat where
  arbitrary = do
    MkSomeLeqNat (n :: SNat n) (m :: SNat m) <- arbitrary
    let m' = Succ m
    case sCmpNat n m' of
      SLT -> pure $ MkSomeLtNat n m'
      _ -> error "impossible"

instance Arbitrary SomeGtNat where
  arbitrary = do
    MkSomeLeqNat (m :: SNat n) (n :: SNat m) <- arbitrary
    let m' = Succ m
    case sCmpNat m' n of
      SGT -> pure $ MkSomeGtNat m' n
      _ -> error "impossible"

test_Lemmas :: TestTree
test_Lemmas =
  testGroup
    "Lemmas"
    [ testProperty @(SomeLeqNat -> Property) "coerceLeqL terminates" $ \(MkSomeLeqNat (_ :: SNat n) sm) -> case coerceLeqL (Refl :: n :~: n) sm Witness of
        Witness -> property True
    , testProperty @(SomeLeqNat -> Property) "coerceLeqR terminates" $ \(MkSomeLeqNat sn (_ :: SNat m)) -> case coerceLeqR sn (Refl :: m :~: m) Witness of
        Witness -> property True
    , testProperty @(SomeSNat -> SomeSNat -> Property) "sLeqCong terminates" $
        \(SomeSNat (_ :: SNat n)) (SomeSNat (_ :: SNat m)) ->
          case sLeqCong (Refl @n) (Refl @m) of
            Refl -> property True
    , testProperty @(SomeSNat -> SomeSNat -> Property) "succDiffNat terminates and gives the correct value" $
        \(SomeSNat sn) (SomeSNat sm) ->
          case succDiffNat sn (sn %+ sm) (DiffNat sn sm) of
            DiffNat sns sms ->
              toNatural (sns %+ sms)
                === toNatural sn + toNatural sm + 1
    , testProperty @(SomeSNat -> SomeSNat -> Property)
        "compareCongR terminates"
        $ \(SomeSNat a) (SomeSNat (_ :: SNat b)) ->
          case compareCongR a (Refl @b) of
            Refl -> property True
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
    , testProperty @(SomeLeqNat -> Property)
        "succLeqToLT terminates"
        $ \(MkSomeLeqNat n' m) ->
          case n' of
            Succ n ->
              case succLeqToLT n m Witness of
                Refl -> property True
            _ -> discard
    , testProperty @(SomeLtNat -> Property)
        "ltToLeq terminates"
        $ \(MkSomeLtNat n m) ->
          case ltToLeq n m Refl of
            Witness -> property True
    , testProperty @(SomeGtNat -> Property)
        "gtToLeq terminates"
        $ \(MkSomeGtNat n m) ->
          case gtToLeq n m Refl of
            Witness -> property True
    ]
