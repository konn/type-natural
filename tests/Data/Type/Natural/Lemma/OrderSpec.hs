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

import Control.Exception (ErrorCall, evaluate, try)
import Data.Functor ((<&>))
import Data.List (isPrefixOf)
import Data.Type.Natural
import Data.Type.Natural.Lemma.Order
import Data.Void (Void)
import Proof.Propositional (IsTrue (Witness))
import Shared ()
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Type.Reflection
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
    MkSomeLeqNat (n :: SNat n) (m :: SNat m) <- arbitrary
    let m' = Succ m
    case sCmpNat m' n of
      SGT -> pure $ MkSomeGtNat m' n
      _ -> error "impossible"

data SomeLeqView where
  MkSomeLeqView :: LeqView n m -> SomeLeqView

instance Show SomeLeqView where
  showsPrec d (MkSomeLeqView (LeqZero n)) =
    showParen (d > 10) $
      showString "LeqZero "
        . showsPrec 11 n
  showsPrec d (MkSomeLeqView (LeqSucc n m w)) =
    showParen (d > 10) $
      showString "LeqSucc "
        . showsPrec 11 n
        . showChar ' '
        . showsPrec 11 m
        . showChar ' '
        . showsPrec 11 w

instance Arbitrary SomeLeqView where
  arbitrary = sized $ \n ->
    if n <= 0
      then
        arbitrary <&> \case
          SomeSNat sn -> MkSomeLeqView (LeqZero sn)
      else
        arbitrary <&> \case
          MkSomeLeqNat sn sm -> MkSomeLeqView $ LeqSucc sn sm Witness

givesImpossibleVoid :: Void -> Property
givesImpossibleVoid contradiction = ioProperty $ do
  eith <- try @ErrorCall $ evaluate contradiction
  case eith of
    Left someE -> do
      pure $ property $ "Impossible" `isPrefixOf` show someE
    Right {} -> pure $ property False

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
          total $ sLeqCong (Refl @n) (Refl @m)
    , testProperty @(SomeSNat -> SomeSNat -> Property) "succDiffNat terminates and gives the correct value" $
        \(SomeSNat sn) (SomeSNat sm) ->
          case succDiffNat sn (sn %+ sm) (DiffNat sn sm) of
            DiffNat sns sms ->
              toNatural (sns %+ sms)
                === toNatural sn + toNatural sm + 1
    , testProperty @(SomeSNat -> SomeSNat -> Property)
        "compareCongR terminates"
        $ \(SomeSNat a) (SomeSNat (_ :: SNat b)) ->
          total $ compareCongR a (Refl @b)
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
          total $ eqlCmpEQ n n Refl
    , testProperty @(SomeSNat -> Property)
        "eqToRefl terminates"
        $ \(SomeSNat n) ->
          total $ eqToRefl n n Refl
    , testProperty @(SomeSNat -> SomeSNat -> Property)
        "flipCmpNat terminates"
        $ \(SomeSNat n) (SomeSNat m) ->
          total $ flipCmpNat n m
    , testProperty @(SomeSNat -> Property)
        "ltToNeq works as expected"
        $ \(SomeSNat n) ->
          givesImpossibleVoid $
            ltToNeq n n (unsafeCoerce $ Refl @()) Refl
    , testProperty @(SomeLeqNat -> Property)
        "leqNeqToLT terminates"
        $ \(MkSomeLeqNat n m) ->
          case n %~ m of
            Equal -> discard
            NonEqual ->
              total $ leqNeqToLT n m Witness (\case {})
    , testProperty @(SomeLeqNat -> Property)
        "succLeqToLT terminates"
        $ \(MkSomeLeqNat n' m) ->
          case n' of
            Succ n ->
              total $ succLeqToLT n m Witness
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
    , testCase "congFlipOrdering" $ do
        Refl <- evaluate (congFlipOrdering (Refl @( 'LT)))
        Refl <- evaluate (congFlipOrdering (Refl @( 'GT)))
        Refl <- evaluate (congFlipOrdering (Refl @( 'EQ)))
        pure ()
    , testProperty @(SomeLtNat -> Property) "ltToSuccLeq terminates" $ \(MkSomeLtNat n m) ->
        case ltToSuccLeq n m Refl of
          Witness -> property True
    , testProperty @(SomeSNat -> Property) "cmpZero terminates" $ \(SomeSNat n) ->
        total $ cmpZero n
    , testProperty @(SomeLeqNat -> Property) "leqToGT terminates" $ \(MkSomeLeqNat b0 a) ->
        case b0 of
          Succ b ->
            total $ leqToGT a b Witness
          Zero -> discard
    , testProperty @(SomeSNat -> Property) "cmpZero' works as expected" $ \(SomeSNat n) ->
        case n of
          Zero -> cmpZero' n === Left Refl
          Succ {} -> case cmpZero' n of
            Right Refl -> property True
            l -> counterexample ("Left Refl expected, but got: " <> show l) False
    , testProperty @(SomeSNat -> Property)
        "zeroNoLT works as expected"
        $ \(SomeSNat n) ->
          givesImpossibleVoid $ zeroNoLT n (unsafeCoerce $ Refl @())
    , testProperty @(SomeLtNat -> Property) "ltRightPredSucc terminates" $ \(MkSomeLtNat a b) ->
        total $ ltRightPredSucc a b Refl
    , testProperty @(SomeSNat -> SomeSNat -> Property) "cmpSucc terminates" $ \(SomeSNat a) (SomeSNat b) ->
        total $ cmpSucc a b
    , testProperty @(SomeSNat -> Property) "ltSucc terminates" $ \(SomeSNat a) ->
        total $ ltSucc a
    , testProperty @(SomeLtNat -> Property) "cmpSuccStepR terminates" $ \(MkSomeLtNat a b) ->
        total $ cmpSuccStepR a b Refl
    , testProperty @(SomeLtNat -> Property) "ltSuccLToLT terminates" $ \(MkSomeLtNat a0 b) ->
        case a0 of
          Succ a -> total $ ltSuccLToLT a b Refl
          Zero -> discard
    , testProperty @(SomeLeqNat -> Property) "leqToLT terminates" $ \(MkSomeLeqNat a0 b) ->
        case a0 of
          Succ a -> total $ leqToLT a b Witness
          Zero -> discard
    , testProperty @(SomeSNat -> Property) "leqZero terminates" $ \(SomeSNat n) ->
        case leqZero n of
          Witness -> property True
    , testProperty @(SomeLeqNat -> Property) "leqSucc terminates" $ \(MkSomeLeqNat n m) ->
        case leqSucc n m Witness of
          Witness -> property True
    , testProperty @(SomeLeqView -> Property) "fromLeqView terminates" $ \(MkSomeLeqView lview) ->
        case fromLeqView lview of
          Witness -> property True
    , testProperty @(SomeSNat -> Property) "leqViewRefl works properly" $ \(SomeSNat sn) ->
        case leqViewRefl sn of
          LeqZero sn' ->
            toNatural sn' === toNatural sn .&&. toNatural sn' === 0
          LeqSucc sn' sm' Witness ->
            toNatural sn' === toNatural sm'
              .&&. toNatural sn' + 1 === toNatural sn
    , testProperty @(SomeLeqNat -> Property) "viewLeq works properly" $ \(MkSomeLeqNat sn sm) ->
        case viewLeq sn sm Witness of
          LeqZero sm' ->
            toNatural sn === 0 .&&. toNatural sm === toNatural sm'
          LeqSucc sn' sm' Witness ->
            toNatural sn' + 1 === toNatural sn
              .&&. toNatural sm' + 1 === toNatural sm
              .&&. toNatural sn' <= toNatural sm'
    , testProperty @(SomeLeqNat -> Property) "leqWitness gives the difference as a witness" $
        \(MkSomeLeqNat sn sm) ->
          case leqWitness sn sm Witness of
            DiffNat sn' delta ->
              toNatural sn === toNatural sn'
                .&&. toNatural sn' + toNatural delta === toNatural sm
    , testProperty @(SomeSNat -> SomeSNat -> Property)
        "leqStep terminates"
        $ \(SomeSNat n) (SomeSNat l) ->
          let m = n %+ l
           in case leqStep n m l Refl of
                Witness -> property True
    ]
