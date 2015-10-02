{-# LANGUAGE CPP, DataKinds, FlexibleContexts, FlexibleInstances, GADTs     #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, NoImplicitPrelude       #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables, StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators                   #-}
{-# LANGUAGE UndecidableInstances                                           #-}
module Data.Type.Natural.Core where
import Data.Singletons
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
import Data.Singletons.Prelude hiding ((:<=), Max, MaxSym0, MaxSym1, MaxSym2,
                                Min, MinSym0, MinSym1, MinSym2, SOrd (..))
import Data.Singletons.TH      (singletons)
#endif
import           Data.Constraint           hiding ((:-))
import           Data.Type.Monomorphic
import           Language.Haskell.TH
import           Language.Haskell.TH.Quote
import           Prelude                   (Bool (..), Eq (..), Int,
                                            Integral (..), Ord ((<)), Show (..),
                                            error, id, otherwise, undefined,
                                            ($), (.))
import qualified Prelude                   as P
import           Proof.Equational
import           Unsafe.Coerce
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 710
import Data.Type.Natural.Definitions hiding ((:<=))
import Prelude                       (Num (..))
#else
import Data.Type.Natural.Definitions
#endif


--------------------------------------------------
-- ** Convenient synonyms
--------------------------------------------------

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
sZ :: SNat Z
sZ = SZ

sS :: SNat n -> SNat (S n)
sS = SS

{-# DEPRECATED sZ, sS "Smart constructors are no longer needed in singletons; Use `SS` or `SZ` instead." #-}
#endif

--------------------------------------------------
-- ** Type-level predicate & judgements.
--------------------------------------------------
-- | Comparison via type-class.
class (n :: Nat) :<= (m :: Nat)
instance Z :<= n
instance (n :<= m) => S n :<= S m

-- | Comparison via GADTs.
data Leq (n :: Nat) (m :: Nat) where
  ZeroLeq     :: SNat m -> Leq Zero m
  SuccLeqSucc :: Leq n m -> Leq (S n) (S m)

type LeqTrueInstance a b = Dict ((a :<<= b) ~ True)

(%-) :: (m :<<= n) ~ True => SNat n -> SNat m -> SNat (n :-: m)
n   %- SZ    = n
SS n %- SS m = n %- m
_    %- _    = error "impossible!"

infixl 6 %-
deriving instance Show (SNat n)
deriving instance Eq (SNat n)

data (a :: Nat) :<: (b :: Nat) where
  ZeroLtSucc :: Zero :<: S m
  SuccLtSucc :: n :<: m -> S n :<: S m

deriving instance Show (a :<: b)

--------------------------------------------------
-- * Total orderings on natural numbers.
--------------------------------------------------
propToBoolLeq :: forall n m. Leq n m -> LeqTrueInstance n m
propToBoolLeq _ = unsafeCoerce (Dict :: Dict ())
{-# INLINE propToBoolLeq #-}

boolToClassLeq :: (n :<<= m) ~ True => SNat n -> SNat m -> LeqInstance n m
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
{-# RULES
 "propToBoolLeq/unsafeCoerce" forall (x :: Leq n m) .
  propToBoolLeq x = unsafeCoerce (Dict :: Dict ()) :: Dict ((n :<<= m) ~ True)
 #-}

boolToClassLeq :: (n :<<= m) ~ True => SNat n -> SNat m -> LeqInstance n m
boolToClassLeq SZ     _      = Dict
boolToClassLeq (SS n) (SS m) = case boolToClassLeq n m of Dict -> Dict
boolToClassLeq _ _ = bugInGHC
{-# RULES
 "boolToClassLeq/unsafeCoerce" forall (n :: SNat n) (m :: SNat m).
  boolToClassLeq n m = unsafeCoerce (Dict :: Dict ()) :: Dict (n :<= m)
 #-}

propToClassLeq :: Leq n m -> LeqInstance n m
propToClassLeq (ZeroLeq _) = Dict
propToClassLeq (SuccLeqSucc leq) = case propToClassLeq leq of Dict -> Dict
{-# RULES
 "propToClassLeq/unsafeCoerce" forall (x :: Leq n m) .
  propToClassLeq x = unsafeCoerce (Dict :: Dict ()) :: Dict (n :<= m)
 #-}
-}

type LeqInstance n m = Dict (n :<= m)

boolToPropLeq :: (n :<<= m) ~ True => SNat n -> SNat m -> Leq n m
boolToPropLeq SZ     m      = ZeroLeq m
boolToPropLeq (SS n) (SS m) = SuccLeqSucc $ boolToPropLeq n m
boolToPropLeq _      _      = bugInGHC

leqRhs :: Leq n m -> SNat m
leqRhs (ZeroLeq m) = m
leqRhs (SuccLeqSucc leq) = sS $ leqRhs leq

leqLhs :: Leq n m -> SNat n
leqLhs (ZeroLeq _) = sZ
leqLhs (SuccLeqSucc leq) = sS $ leqLhs leq
