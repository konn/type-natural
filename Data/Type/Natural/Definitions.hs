{-# LANGUAGE CPP, DataKinds, DeriveDataTypeable, EmptyCase                 #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, GADTs, InstanceSigs      #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, PolyKinds, RankNTypes  #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators, UndecidableInstances #-}
module Data.Type.Natural.Definitions
       (module Data.Type.Natural.Definitions,
        module Data.Singletons.Prelude,
        module Data.Type.Natural.Singleton.Compat
       ) where
import Data.Type.Natural.Singleton.Compat

import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import Data.Typeable

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
  instance Ord Nat where
     Z   <= _   = True
     S _ <= Z   = False
     S n <= S m = n <= m

     n >= m = m   <= n
     n <  m = S n <= m
     n >  m = m   < n

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
  instance Num Nat where
    Z   + n = n
    S m + n = S (m + n)

    n   - Z   = n
    S n - S m = n - m
    Z   - S _ = Z

    Z   * _ = Z
    S n * m = n * m + m

    abs n = n

    signum Z     = Z
    signum (S _) = S Z

    fromInteger n = if n == 0 then Z else S (fromInteger (n-1))
 |]

singletons [d|
  instance Enum Nat where
    succ = S
    pred Z     = Z
    pred (S n) = n
    toEnum n = if n == 0 then Z else S (toEnum (n - 1))
    fromEnum Z     = 0
    fromEnum (S n) = 1 + fromEnum n
 |]

singletons [d|
 (**) :: Nat -> Nat -> Nat
 _ ** Z = S Z
 n ** S m = (n ** m) * n
 |]
#if !MIN_VERSION_singletons(2,4,0)
type (**) a b = a :** b

(%**) :: SNat n -> SNat m -> SNat (n ** m)
(%**) = (%:**)
#endif

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
