{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wall #-}

module Main where

import Data.Type.Natural
import Data.Type.Ordinal

twelve :: SNat 12
twelve = sNat @4 %* sNat @3

-- >>> 15 :: Ordinal 0
