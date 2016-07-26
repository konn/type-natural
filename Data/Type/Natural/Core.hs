{-# LANGUAGE CPP, DataKinds, FlexibleContexts, FlexibleInstances, GADTs #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, NoImplicitPrelude   #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables                 #-}
{-# LANGUAGE StandaloneDeriving, TemplateHaskell, TypeFamilies          #-}
{-# LANGUAGE TypeOperators, UndecidableInstances                        #-}
module Data.Type.Natural.Core where
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
import Data.Type.Natural.Compat
#endif

import Data.Constraint               hiding ((:-))
import Data.Type.Natural.Definitions hiding ((:<=))
import Prelude                       (Bool (..), Eq (..), Show (..), ($))
import Unsafe.Coerce

--------------------------------------------------
-- ** Type-level predicate & judgements.
--------------------------------------------------
-- | Comparison via type-class.
class (n :: Nat) :<= (m :: Nat)
instance 'Z :<= n
instance (n :<= m) => 'S n :<= 'S m

-- | Comparison via GADTs.
data Leq (n :: Nat) (m :: Nat) where
  ZeroLeq     :: SNat m -> Leq Zero m
  SuccLeqSucc :: Leq n m -> Leq ('S n) ('S m)

type LeqTrueInstance a b = Dict ((a :<<= b) ~ 'True)

(%-) :: (m :<<= n) ~ 'True => SNat n -> SNat m -> SNat (n :-: m)
n   %- SZ    = n
SS n %- SS m = n %- m
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
_    %- _    = bugInGHC
#endif

infixl 6 %-
deriving instance Show (SNat n)
deriving instance Eq (SNat n)

data (a :: Nat) :<: (b :: Nat) where
  ZeroLtSucc :: Zero :<: 'S m
  SuccLtSucc :: n :<: m -> 'S n :<: 'S m

deriving instance Show (a :<: b)

--------------------------------------------------
-- * Total orderings on natural numbers.
--------------------------------------------------
propToBoolLeq :: forall n m. Leq n m -> LeqTrueInstance n m
propToBoolLeq _ = unsafeCoerce (Dict :: Dict ())
{-# INLINE propToBoolLeq #-}

boolToClassLeq :: (n :<<= m) ~ 'True => SNat n -> SNat m -> LeqInstance n m
boolToClassLeq _ = unsafeCoerce (Dict :: Dict ())
{-# INLINE boolToClassLeq #-}

propToClassLeq :: Leq n m -> LeqInstance n m
propToClassLeq _ = unsafeCoerce (Dict :: Dict ())
{-# INLINE propToClassLeq #-}

{-
-- | Below is the "proof" of the correctness of above:
propToBoolLeq :: Leq n m -> LeqTrueInstance n m
propToBoolLeq (ZeroLeq _) = Dict
propToBoolLeq (SuccLeqSucc leq) = case propToBoolLeq leq of Dict -> Dict

boolToClassLeq :: (n :<<= m) ~ True => SNat n -> SNat m -> LeqInstance n m
boolToClassLeq SZ     _      = Dict
boolToClassLeq (SS n) (SS m) = case boolToClassLeq n m of Dict -> Dict
boolToClassLeq _ _ = bugInGHC

propToClassLeq :: Leq n m -> LeqInstance n m
propToClassLeq (ZeroLeq _) = Dict
propToClassLeq (SuccLeqSucc leq) = case propToClassLeq leq of Dict -> Dict
-}

type LeqInstance n m = Dict (n :<= m)

boolToPropLeq :: (n :<<= m) ~ 'True => SNat n -> SNat m -> Leq n m
boolToPropLeq SZ     m      = ZeroLeq m
boolToPropLeq (SS n) (SS m) = SuccLeqSucc $ boolToPropLeq n m
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
boolToPropLeq _      _     = bugInGHC
#endif

leqRhs :: Leq n m -> SNat m
leqRhs (ZeroLeq m) = m
leqRhs (SuccLeqSucc leq) = SS $ leqRhs leq

leqLhs :: Leq n m -> SNat n
leqLhs (ZeroLeq _) = SZ
leqLhs (SuccLeqSucc leq) = SS $ leqLhs leq
