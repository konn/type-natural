{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Data.Type.NaturalSpec.TH where

import Data.Type.Natural
import Language.Haskell.TH
import Numeric.Natural
import Shared
import Test.Tasty
import Test.Tasty.HUnit

allCombs :: [(Integer, Integer)]
allCombs = [(n, m) | n <- range, m <- range]

range :: [Integer]
range = [0] ++ [50] ++ [63 .. 65] ++ [98, 99, 100, 200] ++ [1024, 1023, 1025]

testUnary :: Bool -> String -> Name -> Name -> ExpQ
testUnary allowZero label tyName singName =
  [|testCase (label ++ ", compared to fixed type-level")|]
    `appE` doE
      [ noBindS
        [|
          demote ($(varE singName) (sNat @($tyN)))
            @?= demote (sing @($(conT tyName) $tyN))
          |]
      | nat <- range
      , let tyN = litT $ numTyLit nat
      , allowZero || nat /= 0
      ]

testBinary :: String -> Name -> Name -> ExpQ
testBinary = testBinaryP (const $ const True)

testBinaryP :: (Integer -> Integer -> Bool) -> String -> Name -> Name -> ExpQ
testBinaryP ok label tyName singName =
  [|testCase (label ++ ", compared to fixed type-level")|]
    `appE` doE
      [ noBindS
        [|
          demote ($(varE singName) (sNat @($tyL)) (sNat @($tyR)))
            @?= demote (sing @($(conT tyName) $tyL $tyR))
          |]
      | l <- range
      , let tyL = litT $ numTyLit l
      , r <- range
      , let tyR = litT $ numTyLit r
      , ok l r
      ]

-- >>> length allCombs
-- 289
