{-# LANGUAGE CPP, ExplicitNamespaces, TemplateHaskell, TypeInType #-}
-- | Compatibility layer for singletons
module Data.Type.Natural.Singleton.Compat
       (
       module Data.Singletons.Prelude.Eq,
       module Data.Singletons.Prelude.Num,
       module Data.Singletons.Prelude.Ord
#if MIN_VERSION_singletons(2,6,0)
       ,SOrdering(..)
#endif
#if !MIN_VERSION_singletons(2,4,0)
       ,module Data.Type.Natural.Singleton.Compat
#endif
       )
       where

#if !MIN_VERSION_singletons(2,4,0)
import Data.Type.Natural.Singleton.Compat.TH
#endif

#if MIN_VERSION_singletons(2,6,0)
import Data.Singletons.Prelude (SOrdering (SEQ, SGT, SLT))
#else

#endif

import Data.Singletons.Prelude.Eq
import Data.Singletons.Prelude.Num
import Data.Singletons.Prelude.Ord

#if !MIN_VERSION_singletons(2,4,0)
generateCompat Nothing ''SOrd "<"
generateCompat Nothing ''SOrd ">"
generateCompat Nothing ''SOrd "<="
generateCompat Nothing ''SOrd ">="

generateCompat Nothing ''SEq "/="
generateCompat Nothing ''SEq "=="

generateCompat Nothing ''SNum "+"
generateCompat Nothing ''SNum "-"
generateCompat Nothing ''SNum "*"
#endif

