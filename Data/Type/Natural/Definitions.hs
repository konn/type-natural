{-# LANGUAGE CPP, DataKinds, DeriveDataTypeable, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, GADTs, KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, PolyKinds  #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators         #-}
{-# LANGUAGE UndecidableInstances                                 #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ > 708
{-# LANGUAGE InstanceSigs #-}
#endif
module Data.Type.Natural.Definitions
       (module Data.Type.Natural.Definitions,
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 710
        module Data.Singletons.Prelude
#endif
       ) where
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
import Data.Singletons.TH (singletons)
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 710
import Data.Singletons.Prelude
import Prelude                 (Num (..), Ord (..))
#else
import Data.Singletons.Prelude hiding ((:<=), Max, MaxSym0, MaxSym1, MaxSym2,
                                Min, MinSym0, MinSym1, MinSym2, SOrd (..))
#endif
import Data.Singletons.TH (singletons)
#endif
import           Data.Constraint           hiding ((:-))
import           Data.Type.Monomorphic
import           Data.Typeable             (Typeable)
import           Language.Haskell.TH
import           Language.Haskell.TH.Quote
import           Prelude                   (Bool (..), Eq (..), Int,
                                            Integral (..), Ord ((<)), Show (..),
                                            error, id, otherwise, undefined,
                                            ($), (.))
import qualified Prelude                   as P
import           Proof.Equational
import           Unsafe.Coerce

--------------------------------------------------
-- * Natural numbers and its singleton type
--------------------------------------------------
singletons [d|
 data Nat = Z | S Nat
            deriving (Show, Eq)
 |]

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
deriving instance Typeable 'S
deriving instance Typeable 'Z
#endif

--------------------------------------------------
-- ** Arithmetic functions.
--------------------------------------------------

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 710
singletons [d|
 -- | Minimum function.
 min :: Nat -> Nat -> Nat
 min Z     Z     = Z
 min Z     (S _) = Z
 min (S _) Z     = Z
 min (S m) (S n) = S (min m n)

 -- | Maximum function.
 max :: Nat -> Nat -> Nat
 max Z     Z     = Z
 max Z     (S n) = S n
 max (S n) Z     = S n
 max (S n) (S m) = S (max n m)

instance P.Num Nat where
  n - m = n - m
  n + m = n + m
  n * m = n * m
  abs = id
  signum Z = Z
  signum _ = S Z
  fromInteger 0             = Z
  fromInteger n | n P.< 0   = error "negative integer"
                | otherwise = S $ P.fromInteger (n P.- 1)

instance P.Ord Nat where
  Z   <= _   = True
  S _ <= Z   = False
  S n <= S m = n <= m

  min = min
  max = max

|]
#else
singletons [d|
  instance P.Ord Nat where
     Z   <= _   = True
     S _ <= Z   = False
     S n <= S m = n <= m

     min Z     Z     = Z
     min Z     (S _) = Z
     min (S _) Z     = Z
     min (S m) (S n) = S (min m n)

     max Z     Z     = Z
     max Z     (S n) = S n
     max (S n) Z     = S n
     max (S n) (S m) = S (max n m)
 |]
#endif

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 710
singletons [d|
  instance P.Num Nat where
    Z   + n = n
    S m + n = S (m + n)

    n   - Z   = n
    S n - S m = n - m
    Z   - S _ = Z

    Z   * _ = Z
    S n * m = n * m + m

    abs n = n

    signum Z = Z
    signum (S n) = S Z

    fromInteger n = if n == 0 then Z else S (fromInteger (n-1))
 |]
#else
singletons [d|
 (+) :: Nat -> Nat -> Nat
 Z   + n = n
 S m + n = S (m + n)

 (-) :: Nat -> Nat -> Nat
 n   - Z   = n
 S n - S m = n - m
 Z   - S _ = Z

 (*) :: Nat -> Nat -> Nat
 Z   * _ = Z
 S n * m = n * m + m
 |]

infixl 6 %:-, -

infixl 6 %:+, :+

infixl 7 :*:, %:*, :*
#endif

type n :-: m = n :- m
type n :+: m = n :+ m

infixl 6 :-:, :+:

singletons [d|
 (**) :: Nat -> Nat -> Nat
 n ** Z = S Z
 n ** S m = (n ** m) * n
 |]


-- | Addition for singleton numbers.
(%+) :: SNat n -> SNat m -> SNat (n :+: m)
(%+) = (%:+)
infixl 6 %+

-- | Type-level multiplication.
type n :*: m = n :* m

-- | Multiplication for singleton numbers.
(%*) :: SNat n -> SNat m -> SNat (n :*: m)
(%*) = (%:*)
infixl 7 %*

-- | Type-level exponentiation.
type n :**: m = n :** m

-- | Exponentiation for singleton numbers.
(%**) :: SNat n -> SNat m -> SNat (n :**: m)
(%**) = (%:**)

singletons [d|
 zero, one, two, three, four, five, six, seven, eight, nine, ten :: Nat
 eleven, twelve, thirteen, fourteen, fifteen, sixteen, seventeen, eighteen, nineteen, twenty :: Nat
 zero      = Z
 one       = S zero
 two       = S one
 three     = S two
 four      = S three
 five      = S four
 six       = S five
 seven     = S six
 eight     = S seven
 nine      = S eight
 ten       = S nine
 eleven    = S ten
 twelve    = S eleven
 thirteen  = S twelve
 fourteen  = S thirteen
 fifteen   = S fourteen
 sixteen   = S fifteen
 seventeen = S sixteen
 eighteen  = S seventeen
 nineteen  = S eighteen
 twenty    = S nineteen
 n0, n1, n2, n3, n4, n5, n6, n7, n8, n9 :: Nat
 n10, n11, n12, n13, n14, n15, n16, n17 :: Nat
 n18, n19, n20 :: Nat
 n0  = zero
 n1  = one
 n2  = two
 n3  = three
 n4  = four
 n5  = five
 n6  = six
 n7  = seven
 n8  = eight
 n9  = nine
 n10 = ten
 n11 = eleven
 n12 = twelve
 n13 = thirteen
 n14 = fourteen
 n15 = fifteen
 n16 = sixteen
 n17 = seventeen
 n18 = eighteen
 n19 = nineteen
 n20 = twenty
 |]

-- | Boolean-valued type-level comparison function.
singletons [d|
 (<<=) :: Nat -> Nat -> Bool
 Z   <<= _   = True
 S _ <<= Z   = False
 S n <<= S m = n <<= m
 |]
