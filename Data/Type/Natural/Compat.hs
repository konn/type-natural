{-# LANGUAGE CPP #-}
module Data.Type.Natural.Compat (bugInGHC) where
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
import Data.Singletons.Prelude (bugInGHC)
#else
bugInGHC :: a
bugInGHC = error "GHC case-analysis error!"
#endif
