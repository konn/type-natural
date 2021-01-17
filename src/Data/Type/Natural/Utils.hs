{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

module Data.Type.Natural.Utils where

import Data.Type.Equality (type (:~:) (..))
import Unsafe.Coerce (unsafeCoerce)

trustMe :: x :~: y
trustMe = unsafeCoerce (Refl @())
