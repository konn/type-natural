{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Data.Type.NaturalSpec where

import Data.Type.Natural
import Data.Type.NaturalSpec.TH
import Math.NumberTheory.Logarithms (naturalLog2, naturalLogBase)
import Numeric.Natural
import GHC.TypeNats
import Shared
import Test.Tasty
import Test.Tasty.QuickCheck
import Control.Monad (join)

test_arith :: TestTree
test_arith =
  testGroup
    "Arithmetic operations on singletons behaves correctly"
    [ testProperty "(+), compared to demoted" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          toNatural (n %+ m) === (natVal n + natVal m)
    , $(testBinary "(+)" ''(+) '(%+))
    , testProperty "(-), compared to demoted" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          disjoin
            [ natVal n < natVal m .&&. toNatural (m %- n) === (natVal m - natVal n)
            , toNatural (n %- m) === (natVal n - natVal m)
            ]
    , $(testBinaryP (>=) "(-)" ''(-) '(%-))
    , testProperty "(*), compared to demoted" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          toNatural (n %* m) === (natVal n * natVal m)
    , $(testBinary "(*)" ''(*) '(%*))
    , testProperty "Div, compared to demoted" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          label "divide by zero" (natVal m === 0)
            .||. toNatural (n `sDiv` m) === (natVal n `div` natVal m)
    , $(testBinaryP (const $ (/= 0)) "Div" ''Div 'sDiv)
    , testProperty "Mod, compared to demoted" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          label "divide by zero" (natVal m === 0)
            .||. toNatural (n `sMod` m) === (natVal n `mod` natVal m)
    , $(testBinaryP (const $ (/= 0)) "Mod" ''Mod 'sMod)
    , testProperty "(^), compared to demoted" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          toNatural (n %^ m) === (natVal n ^ natVal m)
    , $(testBinaryP (\a b -> a /= 0 && b /= 0) "(^)" ''(^) '(%^))
    , testProperty "(-.), compared to demoted" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          toNatural (n %-. m) === (if natVal n < natVal m then 0 else natVal n - natVal m)
    , $(testBinary "(-.)" ''(-.) '(%-.))
    , testProperty "Log2" $ \(SomeSNat n) ->
        tabulateDigits [natVal n] $
          label "undefined" (natVal n === 0)
            .||. toNatural (sLog2 n) === fromIntegral (naturalLog2 (natVal n))
    , $(testUnary False "Log2" ''Log2 'sLog2)
    , testProperty "succ" $ \(SomeSNat n) ->
        tabulateDigits [natVal n] $
          toNatural (sSucc n) === succ (natVal n)
    , $(testUnary True "Succ" ''Succ 'sSucc)
    , testProperty "pred" $ \(SomeSNat n) ->
        tabulateDigits [natVal n] $
          label "undefiend" (natVal n === 0)
            .||. toNatural (sPred n) === pred (natVal n)
    , $(testUnary False "Pred" ''Pred 'sPred)
    ]

demoteBool :: SBool b -> Bool
demoteBool SFalse = False
demoteBool STrue = True

demoteOrdering :: SOrdering sord -> Ordering
demoteOrdering SLT = LT
demoteOrdering SEQ = EQ
demoteOrdering SGT = GT

test_order :: TestTree
test_order =
  testGroup
    "Order operations on singletons coincides with expression-leven ops"
    [ testProperty "(<=?)" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          demoteBool (n %<=? m) === (natVal n <= natVal m)
    , $(testBinary "(<=?)" ''(<=?) '(%<=?))
    , testProperty "(<?)" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          demoteBool (n %<? m) === (natVal n < natVal m)
    , $(testBinary "(<?)" ''(<?) '(%<?))
    , testProperty "(>=?)" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          demoteBool (n %>=? m) === (natVal n >= natVal m)
    , $(testBinary "(>=?)" ''(>=?) '(%>=?))
    , testProperty "(>?)" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          demoteBool (n %>? m) === (natVal n > natVal m)
    , $(testBinary "(>?)" ''(>?) '(%>?))
    , testProperty "sCmpNat" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          demoteOrdering (n `sCmpNat` m) === compare (natVal n) (natVal m)
    , $(testBinary "CmpNat" ''CmpNat 'sCmpNat)
    , testProperty "min" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          toNatural (n `sMin` m) === (natVal n `min` natVal m)
    , $(testBinary "min" ''Min 'sMin)
    , testProperty "max" $ \(SomeSNat n) (SomeSNat m) ->
        tabulateDigits [natVal n, natVal m] $
          toNatural (n `sMax` m) === (natVal n `max` natVal m)
    , $(testBinary "max" ''Max 'sMax)
    ]

tabulateDigits :: Testable prop => [Natural] -> prop -> Property
tabulateDigits =
  tabulate
    "# of input digits"
    . map (show . succ . naturalLogBase 10 . (+ 1))
