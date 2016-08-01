{-# LANGUAGE DataKinds, DeriveDataTypeable, FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances, GADTs, InstanceSigs, KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses, NoImplicitPrelude, PolyKinds    #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, TypeOperators           #-}
{-# LANGUAGE UndecidableInstances                                   #-}
module Data.Type.Natural.Definitions
       (module Data.Type.Natural.Definitions,
        module Data.Singletons.Prelude
       ) where
import           Data.Singletons.Prelude
import           Data.Singletons.TH      (singletons)
import           Data.Typeable           (Typeable)
import           Prelude                 (Num (..), Ord (..))
import           Prelude                 (Bool (..), Eq (..), Show (..))
import qualified Prelude                 as P



--------------------------------------------------
-- * Natural numbers and its singleton type
--------------------------------------------------
singletons [d|
 data Nat = Z | S Nat
            deriving (Show, Eq)
 |]

deriving instance Typeable 'S
deriving instance Typeable 'Z

--------------------------------------------------
-- ** Arithmetic functions.
--------------------------------------------------

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
    signum (S _) = S Z

    fromInteger n = if n == 0 then Z else S (fromInteger (n-1))
 |]

type n :-: m = n :- m
type n :+: m = n :+ m

infixl 6 :-:, :+:

singletons [d|
 (**) :: Nat -> Nat -> Nat
 _ ** Z = S Z
 n ** S m = (n ** m) * n
 |]


-- | Addition for singleton numbers.
(%+) :: SNat n -> SNat m -> SNat (n :+: m)
(%+) = (%:+)
infixl 6 %+

-- | Type-level multiplication.
type n :*: m = n :* m
infixl 7 :*:

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
{-# DEPRECATED (<<=) "Use @'Ord'@ instance instead." #-}
(<<=) :: Nat -> Nat -> Bool
(<<=) = (<=)

{-# DEPRECATED (:<<=) "Use @'(:<=)'@ from @'POrd'@ instead." #-}
type n :<<= m = n :<= m

{-# DEPRECATED (%:<<=) "Use @'(%:<=)'@ from @'POrd'@ instead." #-}
(%:<<=) :: SNat n -> SNat m -> SBool (n :<<= m)
(%:<<=) = (%:<=)

type (:<<=$) = (:<=$)
{-# DEPRECATED (:<<=$) "Use @(':<=$')@ instead." #-}

type (:<<=$$) = (:<=$$)
{-# DEPRECATED (:<<=$$) "Use @(':<=$$')@ instead." #-}

type (:<<=$$$) n m = (:<=$$$) n m
{-# DEPRECATED (:<<=$$$) "Use @(':<=$$$')@ instead." #-}
