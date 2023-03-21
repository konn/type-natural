{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Type.Natural.Lemma.OrderSpec where

import Control.Exception (SomeException (..), evaluate, try)
import Data.Functor ((<&>))
import Data.List (isInfixOf, isPrefixOf)
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
  MkSomeLeqNat :: (n <=? m) ~ 'True => SNat n -> SNat m -> SomeLeqNat

data SomeLtNat where
  MkSomeLtNat ::
    CmpNat n m ~ 'LT =>
    SNat n ->
    SNat m ->
    SomeLtNat

data SomeLneqNat where
  MkSomeLneqNat ::
    (n <? m) ~ 'True =>
    SNat n ->
    SNat m ->
    SomeLneqNat

data SomeGtNat where
  MkSomeGtNat ::
    CmpNat n m ~ 'GT =>
    SNat n ->
    SNat m ->
    SomeGtNat

deriving instance Show SomeLeqNat

deriving instance Show SomeLtNat

deriving instance Show SomeLneqNat

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

instance Arbitrary SomeLneqNat where
  arbitrary = do
    MkSomeLtNat (n :: SNat n) (m :: SNat m) <- arbitrary
    let m' = Succ m
    case n %<? m' of
      STrue -> pure $ MkSomeLneqNat n m'
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
  eith <- try @SomeException $ evaluate contradiction
  case eith of
    Left someE -> do
      pure $ counterexample (show someE) $
        property $
          "Impossible" `isPrefixOf` show someE
            || "Non-exhaustive" `isInfixOf` show someE
            || "missingAlt" `isInfixOf` show someE
    Right v -> 
      pure $ counterexample "Value of void returned..." 
        $ property False

test_Lemmas :: TestTree
test_Lemmas =
  testGroup
    "Lemmas"
    [ testProperty @(SomeLeqNat -> Property) "coerceLeqL terminates" $ \(MkSomeLeqNat (_ :: SNat n) sm) -> totalWitness $ coerceLeqL (Refl :: n :~: n) sm Witness
    , testProperty @(SomeLeqNat -> Property) "coerceLeqR terminates" $ \(MkSomeLeqNat sn (_ :: SNat m)) -> totalWitness $ coerceLeqR sn (Refl :: m :~: m) Witness
    , testProperty @(SomeSNat -> SomeSNat -> Property) "sLeqCong terminates" $
        \(SomeSNat (_ :: SNat n)) (SomeSNat (_ :: SNat m)) ->
          totalRefl $ sLeqCong (Refl @n) (Refl @m)
    , testProperty @(SomeSNat -> SomeSNat -> Property) "succDiffNat terminates and gives the correct value" $
        \(SomeSNat sn) (SomeSNat sm) ->
          case succDiffNat sn (sn %+ sm) (DiffNat sn sm) of
            DiffNat sns sms ->
              fromSNat (sns %+ sms)
                === fromSNat sn + fromSNat sm + 1
    , testProperty @(SomeSNat -> SomeSNat -> Property)
        "compareCongR terminates"
        $ \(SomeSNat a) (SomeSNat (_ :: SNat b)) ->
          totalRefl $ compareCongR a (Refl @b)
    , testProperty @(SomeLeqNat -> Property)
        "leqToCmp works properly"
        $ \case
          MkSomeLeqNat a b ->
            case leqToCmp a b Witness of
              Left Refl -> fromSNat a === fromSNat b
              Right Refl ->
                property $ fromSNat a < fromSNat b
    , testProperty @(SomeSNat -> Property)
        "eqlCmpEQ terminates"
        $ \(SomeSNat n) ->
          totalRefl $ eqlCmpEQ n n Refl
    , testProperty @(SomeSNat -> Property)
        "eqToRefl terminates"
        $ \(SomeSNat n) ->
          totalRefl $ eqToRefl n n Refl
    , testProperty @(SomeSNat -> SomeSNat -> Property)
        "flipCmpNat terminates"
        $ \(SomeSNat n) (SomeSNat m) ->
          totalRefl $ flipCmpNat n m
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
              totalRefl $ leqNeqToLT n m Witness (\case {})
    , testProperty @(SomeLeqNat -> Property)
        "succLeqToLT terminates"
        $ \(MkSomeLeqNat n' m) ->
          case n' of
            Succ n ->
              totalRefl $ succLeqToLT n m Witness
            _ -> discard
    , testProperty @(SomeLtNat -> Property)
        "ltToLeq terminates"
        $ \(MkSomeLtNat n m) ->
          totalWitness $ ltToLeq n m Refl
    , testProperty @(SomeGtNat -> Property)
        "gtToLeq terminates"
        $ \(MkSomeGtNat n m) ->
          totalWitness $ gtToLeq n m Refl
    , testCase "congFlipOrdering" $ do
        Refl <- evaluate (congFlipOrdering (Refl @( 'LT)))
        Refl <- evaluate (congFlipOrdering (Refl @( 'GT)))
        Refl <- evaluate (congFlipOrdering (Refl @( 'EQ)))
        pure ()
    , testProperty @(SomeLtNat -> Property) "ltToSuccLeq terminates" $ \(MkSomeLtNat n m) ->
        totalWitness $ ltToSuccLeq n m Refl
    , testProperty @(SomeSNat -> Property) "cmpZero terminates" $ \(SomeSNat n) ->
        totalRefl $ cmpZero n
    , testProperty @(SomeLeqNat -> Property) "leqToGT terminates" $ \(MkSomeLeqNat b0 a) ->
        case b0 of
          Succ b ->
            totalRefl $ leqToGT a b Witness
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
        totalRefl $ ltRightPredSucc a b Refl
    , testProperty @(SomeSNat -> SomeSNat -> Property) "cmpSucc terminates" $ \(SomeSNat a) (SomeSNat b) ->
        totalRefl $ cmpSucc a b
    , testProperty @(SomeSNat -> Property) "ltSucc terminates" $ \(SomeSNat a) ->
        totalRefl $ ltSucc a
    , testProperty @(SomeLtNat -> Property) "cmpSuccStepR terminates" $ \(MkSomeLtNat a b) ->
        totalRefl $ cmpSuccStepR a b Refl
    , testProperty @(SomeLtNat -> Property) "ltSuccLToLT terminates" $ \(MkSomeLtNat a0 b) ->
        case a0 of
          Succ a -> totalRefl $ ltSuccLToLT a b Refl
          Zero -> discard
    , testProperty @(SomeLeqNat -> Property) "leqToLT terminates" $ \(MkSomeLeqNat a0 b) ->
        case a0 of
          Succ a -> totalRefl $ leqToLT a b Witness
          Zero -> discard
    , testProperty @(SomeSNat -> Property) "leqZero terminates" $ \(SomeSNat n) ->
        totalWitness $ leqZero n
    , testProperty @(SomeLeqNat -> Property) "leqSucc terminates" $ \(MkSomeLeqNat n m) ->
        totalWitness $ leqSucc n m Witness
    , testProperty @(SomeLeqView -> Property) "fromLeqView terminates" $ \(MkSomeLeqView lview) ->
        totalWitness $ fromLeqView lview
    , testProperty @(SomeSNat -> Property) "leqViewRefl works properly" $ \(SomeSNat sn) ->
        case leqViewRefl sn of
          LeqZero sn' ->
            fromSNat sn' === fromSNat sn .&&. fromSNat sn' === 0
          LeqSucc sn' sm' Witness ->
            fromSNat sn' === fromSNat sm'
              .&&. fromSNat sn' + 1 === fromSNat sn
    , testProperty @(SomeLeqNat -> Property) "viewLeq works properly" $ \(MkSomeLeqNat sn sm) ->
        case viewLeq sn sm Witness of
          LeqZero sm' ->
            fromSNat sn === 0 .&&. fromSNat sm === fromSNat sm'
          LeqSucc sn' sm' Witness ->
            fromSNat sn' + 1 === fromSNat sn
              .&&. fromSNat sm' + 1 === fromSNat sm
              .&&. fromSNat sn' <= fromSNat sm'
    , testProperty @(SomeLeqNat -> Property) "leqWitness gives the difference as a witness" $
        \(MkSomeLeqNat sn sm) ->
          case leqWitness sn sm Witness of
            DiffNat sn' delta ->
              fromSNat sn === fromSNat sn'
                .&&. fromSNat sn' + fromSNat delta === fromSNat sm
    , testProperty @(SomeSNat -> SomeSNat -> Property)
        "leqStep terminates"
        $ \(SomeSNat n) (SomeSNat l) ->
          let m = n %+ l
           in totalWitness $ leqStep n m l Refl
    , testProperty @(SomeLeqNat -> Property) "leqNeqToSuccLeq terminates" $
        \(MkSomeLeqNat n m) ->
          case n %~ m of
            Equal -> discard
            NonEqual ->
              totalWitness $ leqNeqToSuccLeq n m Witness (\case {})
    , testProperty @(SomeSNat -> Property) "leqRefl terminates" $
        \(SomeSNat n) ->
          totalWitness $ leqRefl n
    , testProperty @(SomeLeqNat -> Property) "leqSuccStepR and leqSuccStepL terminates" $
        \(MkSomeLeqNat n m) ->
          totalWitness (leqSuccStepR n m Witness)
            .&&. case n of
              Succ n' ->
                label "leqSuccStepL tested" $
                  totalWitness (leqSuccStepL n' m Witness)
              _ -> property True
    , testProperty @(SomeSNat -> Property) "leqReflexive terminates" $
        \(SomeSNat n) ->
          totalWitness $ leqReflexive n n Refl
    , testProperty @(SomeLeqNat -> SomeSNat -> Property) "leqTrans terminates" $
        \(MkSomeLeqNat (n :: SNat n) (m :: SNat m)) (SomeSNat (l0 :: SNat lMinsM)) ->
          let l = m %+ l0
           in case m %<=? l of
                STrue ->
                  totalWitness $
                    leqTrans n m l Witness (Witness :: IsTrue (m <=? (m + lMinsM)))
                SFalse -> error "impossible"
    , testProperty @(SomeSNat -> Property) "leqAntisymm terminates" $
        \(SomeSNat n) ->
          totalRefl $ leqAntisymm n n Witness Witness
    , testProperty @(SomeLeqNat -> SomeLeqNat -> Property) "plusMonotone terminates" $
        \(MkSomeLeqNat n m) (MkSomeLeqNat l k) ->
          totalWitness $ plusMonotone n m l k Witness Witness
    , testCase "leqZeroElim terminates" $
        leqZeroElim (sNat @0) Witness @?= Refl
    , testProperty @(SomeLeqNat -> SomeSNat -> Property) "plusMonotoneL terminates" $
        \(MkSomeLeqNat n m) (SomeSNat l) ->
          totalWitness $ plusMonotoneL n m l Witness
    , testProperty @(SomeLeqNat -> SomeSNat -> Property) "plusMonotoneR terminates" $
        \(MkSomeLeqNat n m) (SomeSNat l) ->
          totalWitness $ plusMonotoneR l n m Witness
    , testProperty @(SomeSNat -> SomeSNat -> Property) "plusLeqL terminates" $
        \(SomeSNat n) (SomeSNat m) ->
          totalWitness $ plusLeqL n m
    , testProperty @(SomeSNat -> SomeSNat -> Property) "plusLeqR terminates" $
        \(SomeSNat n) (SomeSNat m) ->
          totalWitness $ plusLeqR n m
    , testProperty @(SomeLeqNat -> SomeSNat -> Property) "plusCancelLeqL terminates" $
        \(MkSomeLeqNat (m :: SNat m) (l :: SNat l)) (SomeSNat n) ->
          totalWitness $
            plusCancelLeqR
              n
              m
              l
              (unsafeCoerce (Witness :: IsTrue (m <=? l)))
    , testProperty @(SomeLeqNat -> SomeSNat -> Property) "plusCancelLeqR terminates" $
        \(MkSomeLeqNat (n :: SNat n) (m :: SNat m)) (SomeSNat l) ->
          totalWitness $
            plusCancelLeqR
              n
              m
              l
              (unsafeCoerce (Witness :: IsTrue (n <=? m)))
    , testProperty @(SomeSNat -> Property) "succLeqZeroAbsurd works properly" $ \(SomeSNat n) ->
        givesImpossibleVoid $ succLeqZeroAbsurd n (unsafeCoerce Witness)
    , testProperty @(SomeSNat -> Property) "succLeqZeroAbsurd' works properly" $ \(SomeSNat n) ->
        totalRefl $ succLeqZeroAbsurd' n
    , testProperty @(SomeSNat -> Property) "succLeqAbsurd works properly" $ \(SomeSNat n) ->
        givesImpossibleVoid $ succLeqAbsurd n (unsafeCoerce Witness)
    , testProperty @(SomeSNat -> Property) "succLeqAbsurd' works properly" $ \(SomeSNat n) ->
        totalRefl $ succLeqAbsurd' n
    , testProperty @(SomeGtNat -> Property)
        "notLeqToLeq terminates"
        $ \(MkSomeGtNat n m) ->
          case n %<=? m of
            STrue -> error "impossible!"
            SFalse ->
              totalWitness $ notLeqToLeq n m
    , testProperty
        @(SomeSNat -> SomeSNat -> Property)
        "leqSucc' terminates"
        $ \(SomeSNat n) (SomeSNat m) ->
          totalRefl $ leqSucc' n m
    , testProperty @(SomeLeqNat -> Property) "leqToMin terminates" $
        \(MkSomeLeqNat n m) ->
          totalRefl $ leqToMin n m Witness
    , testProperty @(SomeLeqNat -> Property) "geqToMin terminates" $
        \(MkSomeLeqNat n m) ->
          totalRefl $ geqToMin m n Witness
    , testProperty @(SomeSNat -> SomeSNat -> Property) "minComm terminates" $
        \(SomeSNat n) (SomeSNat m) ->
          totalRefl $ minComm n m
    , testProperty @(SomeSNat -> SomeSNat -> Property) "minLeqL terminates" $
        \(SomeSNat n) (SomeSNat m) ->
          totalWitness $ minLeqL n m
    , testProperty @(SomeSNat -> SomeSNat -> Property) "minLeqR terminates" $
        \(SomeSNat n) (SomeSNat m) ->
          totalWitness $ minLeqR n m
    , testProperty @(SomeLeqNat -> SomeSNat -> Property) "minLargest terminates" $
        \(MkSomeLeqNat l n) (SomeSNat lm) ->
          let m = l %+ lm
           in totalWitness $
                minLargest l n m Witness (unsafeCoerce Witness)
    , testProperty @(SomeLeqNat -> Property) "leqToMax termaxates" $
        \(MkSomeLeqNat n m) ->
          totalRefl $ leqToMax n m Witness
    , testProperty @(SomeLeqNat -> Property) "geqToMax termaxates" $
        \(MkSomeLeqNat n m) ->
          totalRefl $ geqToMax m n Witness
    , testProperty @(SomeSNat -> SomeSNat -> Property) "maxComm termaxates" $
        \(SomeSNat n) (SomeSNat m) ->
          totalRefl $ maxComm n m
    , testProperty @(SomeSNat -> SomeSNat -> Property) "maxLeqL termaxates" $
        \(SomeSNat n) (SomeSNat m) ->
          totalWitness $ maxLeqL n m
    , testProperty @(SomeSNat -> SomeSNat -> Property) "maxLeqR termaxates" $
        \(SomeSNat n) (SomeSNat m) ->
          totalWitness $ maxLeqR n m
    , testProperty @(SomeLeqNat -> Property) "maxLeast termaxates" $
        \(MkSomeLeqNat n l) ->
          forAll (elements [0 .. fromSNat l]) $ \m0 ->
            case toSomeSNat m0 of
              SomeSNat m ->
                totalWitness $
                  maxLeast l n m Witness (unsafeCoerce Witness)
    , testProperty @(SomeSNat -> SomeSNat -> Property) "lneqSuccLeq terminates" $
        \(SomeSNat n) (SomeSNat m) ->
          totalRefl $ lneqSuccLeq n m
    , testProperty @(SomeSNat -> SomeSNat -> Property) "lneqReversed terminates" $
        \(SomeSNat n) (SomeSNat m) ->
          totalRefl $ lneqReversed n m
    , testProperty @(SomeLneqNat -> Property) "lneqToLT terminates" $
        \(MkSomeLneqNat n m) ->
          totalRefl $ lneqToLT n m Witness
    , testProperty @(SomeLtNat -> Property) "ltToLneq terminates" $
        \(MkSomeLtNat n m) ->
          totalWitness $ ltToLneq n m Refl
    , testProperty @(SomeSNat -> Property) "lneqZero terminates" $
        \(SomeSNat n) -> totalWitness $ lneqZero n
    , testProperty @(SomeSNat -> Property) "lneqSucc terminates" $
        \(SomeSNat n) -> totalWitness $ lneqSucc n
    , testProperty @(SomeSNat -> SomeSNat -> Property) "succLneqSucc terminates" $
        \(SomeSNat n) (SomeSNat m) -> totalRefl $ succLneqSucc n m
    , testProperty @(SomeLneqNat -> Property) "lneqRightPredSucc terminates" $
        \(MkSomeLneqNat n m) ->
          totalRefl $ lneqRightPredSucc n m Witness
    , testProperty @(SomeLneqNat -> Property) "lneqSuccStepL and lneqSuccStepR works properly" $
        \(MkSomeLneqNat n m) ->
          conjoin
            [ totalWitness (lneqSuccStepR n m Witness)
            , case n of
                Succ n' ->
                  label "lneqSuccStepL checked" $
                    totalWitness (lneqSuccStepL n' m Witness)
                Zero -> property True
            ]
    , testProperty @(SomeLneqNat -> SomeLneqNat -> Property)
        "plusStrictMonotone terminates"
        $ \(MkSomeLneqNat n m) (MkSomeLneqNat l k) ->
          totalWitness $
            plusStrictMonotone n m l k Witness Witness
    , testProperty @(SomeSNat -> Property) "maxZeroL terminates" $
        \(SomeSNat n) -> totalRefl $ maxZeroL n
    , testProperty @(SomeSNat -> Property) "maxZeroR terminates" $
        \(SomeSNat n) -> totalRefl $ maxZeroR n
    , testProperty @(SomeSNat -> Property) "minZeroL terminates" $
        \(SomeSNat n) -> totalRefl $ minZeroL n
    , testProperty @(SomeSNat -> Property) "minZeroR terminates" $
        \(SomeSNat n) -> totalRefl $ minZeroR n
    , testProperty @(SomeLeqNat -> Property) "minusSucc terminates" $
        \(MkSomeLeqNat m n) ->
          totalRefl $ minusSucc n m Witness
    , testProperty @(SomeSNat -> Property) "lneqZeroAbsurd is absurd" $
        \(SomeSNat n) ->
          givesImpossibleVoid $
            lneqZeroAbsurd n $ unsafeCoerce Witness
    , testProperty @(SomeLeqNat -> Property)
        "minusPlus terminates"
        $ \(MkSomeLeqNat m n) ->
          totalRefl $
            minusPlus n m Witness
    , testProperty @(SomeSNat -> SomeSNat -> Property)
        "minPlusTruncMinus terminates"
        $ \(SomeSNat n) (SomeSNat m) ->
          totalRefl $ minPlusTruncMinus n m
    , testProperty @(SomeSNat -> SomeSNat -> Property)
        "truncMinusLeq terminates"
        $ \(SomeSNat n) (SomeSNat m) ->
          totalWitness $ truncMinusLeq n m
    , testProperty @(SomeSNat -> SomeSNat -> Property)
      "leqOrdCond terminates"
      $ \(SomeSNat n) (SomeSNat m) -> totalRefl $ leqOrdCond n m
    , testProperty @(SomeSNat -> Property)
      "cmpSuccZeroGT terminates"
      $ \(SomeSNat n) -> totalRefl $ cmpSuccZeroGT n
    ]

totalWitness :: IsTrue p -> Property
totalWitness w =
  counterexample "Witness is not totalRefl!" $
    within
      10000
      ( (case w of Witness -> True :: Bool) ::
          Bool
      )

totalRefl :: a :~: b -> Property
totalRefl = within 10000 . total
