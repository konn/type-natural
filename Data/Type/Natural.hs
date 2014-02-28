{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances, GADTs    #-}
{-# LANGUAGE KindSignatures, MultiParamTypeClasses, NoImplicitPrelude #-}
{-# LANGUAGE PolyKinds, RankNTypes, TemplateHaskell, TypeFamilies     #-}
{-# LANGUAGE TypeOperators, UndecidableInstances, StandaloneDeriving  #-}
-- | Type level peano natural number, some arithmetic functions and their singletons.
module Data.Type.Natural (-- * Re-exported modules.
                          module Data.Singletons,
                          -- * Natural Numbers
                          -- | Peano natural numbers. It will be promoted to the type-level natural number.
                          Nat(..),
                          -- | Singleton type for 'Nat'.
                          SNat, Sing (SZ, SS),
                          -- ** Smart constructors
                          sZ, sS,
                          -- ** Arithmetic functions and their singletons.
                          min, Min, sMin, max, Max, sMax,
                          (:+:), (:+), (%+), (%:+), (:*:), (:*), (%:*), (%*),
                          (:-:), (:-), (%:-), (%-),
                          -- ** Type-level predicate & judgements
                          Leq(..), (:<=), (:<<=), (%:<<=), LeqInstance,
                          boolToPropLeq, boolToClassLeq, propToClassLeq,
                          LeqTrueInstance, propToBoolLeq,
                          -- * Conversion functions
                          natToInt, intToNat, sNatToInt,
                          -- * Quasi quotes for natural numbers
                          nat, snat,
                          -- * Properties of natural numbers
                          succCongEq, plusCongR, plusCongL, succPlusL, succPlusR,
                          plusZR, plusZL, eqPreservesS, plusAssociative,
                          multAssociative, multComm, multZL, multZR, multOneL, multOneR,
                          plusMultDistr, multPlusDistr, multCongL, multCongR,
                          sAndPlusOne, plusCommutative, minusCongEq, minusNilpotent,
                          eqSuccMinus, plusMinusEqL, plusMinusEqR,
                          zAbsorbsMinR, zAbsorbsMinL, plusSR,
                          leqRhs, leqLhs, minComm, maxZL, maxComm, maxZR,
                          -- * Properties of ordering 'Leq'
                          leqRefl, leqSucc, leqTrans, plusMonotone, plusLeqL, plusLeqR,
                          minLeqL, minLeqR, leqAnitsymmetric, maxLeqL, maxLeqR,
                          leqSnZAbsurd, leqnZElim, leqSnLeq, leqPred, leqSnnAbsurd,
                          -- * Useful type synonyms and constructors
                          zero, one, two, three, four, five, six, seven, eight, nine, ten, eleven,
                          twelve, thirteen, fourteen, fifteen, sixteen, seventeen, eighteen, nineteen, twenty,
                          Zero, One, Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten,
                          Eleven, Twelve, Thirteen, Fourteen, Fifteen, Sixteen, Seventeen, Eighteen, Nineteen, Twenty,
                          sZero, sOne, sTwo, sThree, sFour, sFive, sSix, sSeven, sEight, sNine, sTen, sEleven,
                          sTwelve, sThirteen, sFourteen, sFifteen, sSixteen, sSeventeen, sEighteen, sNineteen, sTwenty,
                          n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19, n20,
                          N0, N1, N2, N3, N4, N5, N6, N7, N8, N9, N10, N11, N12, N13, N14, N15, N16, N17, N18, N19, N20,
                          sN0, sN1, sN2, sN3, sN4, sN5, sN6, sN7, sN8, sN9, sN10, sN11, sN12, sN13, sN14,
                          sN15, sN16, sN17, sN18, sN19, sN20
                         ) where
import           Data.Singletons
import           Data.Type.Monomorphic
import           Prelude          (Int, Bool (..), Eq (..), Integral (..), Ord ((<)),
                                   Show (..), error, id, otherwise, ($), (.), undefined)
import qualified Prelude          as P
import           Proof.Equational
import Data.Constraint hiding ((:-))
import Language.Haskell.TH.Quote
import Unsafe.Coerce
import Language.Haskell.TH

--------------------------------------------------
-- * Natural numbers and its singleton type
--------------------------------------------------
singletons [d|
 data Nat = Z | S Nat
            deriving (Show, Eq, Ord)
 |]

--------------------------------------------------
-- ** Arithmetic functions.
--------------------------------------------------

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
 |]

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

infixl 6 :-:, %:-, -

type n :-: m = n :- m
infixl 6 :+:, %+, %:+, :+

type n :+: m = n :+ m

-- | Addition for singleton numbers.
(%+) :: SNat n -> SNat m -> SNat (n :+: m)
(%+) = (%:+)

infixl 7 :*:, %*, %:*, :*

-- | Type-level multiplication.
type n :*: m = n :* m

-- | Multiplication for singleton numbers.
(%*) :: SNat n -> SNat m -> SNat (n :*: m)
(%*) = (%:*)

--------------------------------------------------
-- ** Convenient synonyms
--------------------------------------------------
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

--------------------------------------------------
-- ** Type-level predicate & judgements.
--------------------------------------------------
-- | Comparison via type-class.
class (n :: Nat) :<= (m :: Nat)
instance Z :<= n
instance (n :<= m) => S n :<= S m

-- | Boolean-valued type-level comparison function.
singletons [d|
 (<<=) :: Nat -> Nat -> Bool
 Z   <<= _   = True
 S _ <<= Z   = False
 S n <<= S m = n <<= m
 |]

-- | Comparison via GADTs.
data Leq (n :: Nat) (m :: Nat) where
  ZeroLeq     :: SNat m -> Leq Zero m
  SuccLeqSucc :: Leq n m -> Leq (S n) (S m)

type LeqTrueInstance a b = Dict ((a :<<= b) ~ True)

(%-) :: (n :<<= m) ~ True => SNat n -> SNat m -> SNat (n :-: m)
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

--------------------------------------------------
-- * Properties
--------------------------------------------------
plusZR :: SNat n -> n :+: Z :=: n
plusZR SZ     = Refl
plusZR (SS n) =
 start (sS n %+ sZ)
   =~= sS (n %+ sZ)
   === sS n          `because` cong' sS (plusZR n)

eqPreservesS :: n :=: m -> S n :=: S m
eqPreservesS Refl = Refl

plusZL :: SNat n -> Z :+: n :=: n
plusZL _ = Refl

succCongEq :: n :=: m -> S n :=: S m
succCongEq Refl = Refl

sAndPlusOne :: SNat n -> S n :=: n :+: One
sAndPlusOne SZ = Refl
sAndPlusOne (SS n) =
  start (sS (sS n))
    === sS (n %+ sOne) `because` cong' sS (sAndPlusOne n)
    =~= sS n %+ sOne

plusAssociative :: SNat n -> SNat m -> SNat l
                -> n :+: (m :+: l) :=: (n :+: m) :+: l
plusAssociative SZ     _ _ = Refl
plusAssociative (SS n) m l =
  start (sS n %+ (m %+ l))
    =~= sS (n %+ (m %+ l))
    === sS ((n %+ m) %+ l)  `because` cong' sS (plusAssociative n m l)
    =~= sS (n %+ m) %+ l
    =~= (sS n %+ m) %+ l

plusSR :: SNat n -> SNat m -> S (n :+: m) :=: n :+: S m
plusSR n m =
  start (sS (n %+ m))
    === (n %+ m) %+ sOne `because` sAndPlusOne (n %+ m)
    === n %+ (m %+ sOne) `because` symmetry (plusAssociative n m sOne)
    === n %+ sS m        `because` plusCongL n (symmetry $ sAndPlusOne m)

plusCongL :: SNat n -> m :=: m' -> n :+ m :=: n :+ m'
plusCongL _ Refl = Refl

plusCongR :: SNat n -> m :=: m' -> m :+ n :=: m' :+ n
plusCongR _ Refl = Refl

succPlusL :: SNat n -> SNat m -> S n :+ m :=: S (n :+ m)
succPlusL _ _ = Refl

succPlusR :: SNat n -> SNat m -> n :+ S m :=: S (n :+ m)
succPlusR SZ     _ = Refl
succPlusR (SS n) m =
  start (sS n %+ sS m)
    =~= sS (n %+ sS m)
    === sS (sS (n %+ m)) `because` succCongEq (succPlusR n m)
    =~= sS (sS n %+ m)

minusCongEq :: n :=: m -> SNat l -> n :-: l :=: m :-: l
minusCongEq Refl _ = Refl

minusNilpotent :: SNat n -> n :-: n :=: Zero
minusNilpotent SZ = Refl
minusNilpotent (SS n) =
  start (sS n %:- sS n)
    =~= n %:- n
    === sZ     `because` minusNilpotent n

plusCommutative :: SNat n -> SNat m -> n :+: m :=: m :+: n
plusCommutative SZ SZ     = Refl
plusCommutative SZ (SS m) =
  start (sZ %+ sS m)
    =~= sS m
    === sS (m %+ sZ) `because` cong' sS (plusCommutative SZ m)
    =~= sS m %+ sZ
plusCommutative (SS n) m =
  start (sS n %+ m)
    =~= sS (n %+ m)
    === sS (m %+ n)      `because` cong' sS (plusCommutative n m)
    === (m %+ n) %+ sOne `because` sAndPlusOne (m %+ n)
    === m %+ (n %+ sOne) `because` symmetry (plusAssociative m n sOne)
    === m %+ sS n        `because` plusCongL m (symmetry $ sAndPlusOne n)

eqSuccMinus :: ((m :<<= n) ~ True)
            => SNat n -> SNat m -> (S n :-: m) :=: (S (n :-: m))
eqSuccMinus _      SZ     = Refl
eqSuccMinus (SS n) (SS m) =
  start (sS (sS n) %:- sS m)
    =~= sS n %:- m
    === sS (n %:- m)       `because` eqSuccMinus n m
    =~= sS (sS n %:- sS m)
eqSuccMinus _ _ = bugInGHC

plusMinusEqL :: SNat n -> SNat m -> ((n :+: m) :-: m) :=: n
plusMinusEqL SZ     m = minusNilpotent m
plusMinusEqL (SS n) m =
  case propToBoolLeq (plusLeqR n m) of
    Dict -> transitivity (eqSuccMinus (n %+ m) m) (eqPreservesS $ plusMinusEqL n m)

plusMinusEqR :: SNat n -> SNat m -> (m :+: n) :-: m :=: n
plusMinusEqR n m = transitivity (minusCongEq (plusCommutative m n) m) (plusMinusEqL n m)

zAbsorbsMinR :: SNat n -> Min n Z :=: Z
zAbsorbsMinR SZ     = Refl
zAbsorbsMinR (SS n) =
  case zAbsorbsMinR n of
    Refl -> Refl

zAbsorbsMinL :: SNat n -> Min Z n :=: Z
zAbsorbsMinL SZ     = Refl
zAbsorbsMinL (SS n) = case zAbsorbsMinL n of Refl -> Refl

minComm :: SNat n -> SNat m -> Min n m :=: Min m n
minComm SZ     SZ = Refl
minComm SZ     (SS _) = Refl
minComm (SS _) SZ = Refl
minComm (SS n) (SS m) = case minComm n m of Refl -> Refl

maxZL :: SNat n -> Max Z n :=: n
maxZL SZ = Refl
maxZL (SS _) = Refl

maxComm :: SNat n -> SNat m -> (Max n m) :=: (Max m n)
maxComm SZ SZ = Refl
maxComm SZ (SS _) = Refl
maxComm (SS _) SZ = Refl
maxComm (SS n) (SS m) = case maxComm n m of Refl -> Refl

maxZR :: SNat n -> Max n Z :=: n
maxZR n = transitivity (maxComm n sZ) (maxZL n)

newtype MultPlusDistr l m n =
    MultPlusDistr { unMultPlusDistr :: l :* (m :+ n) :=: l :* m :+ l :* n}

instance Proposition (MultPlusDistr l m) where
  type OriginalProp (MultPlusDistr l m) n = l :* (m :+ n) :=: l :* m :+ l :* n
  wrap = MultPlusDistr
  unWrap = unMultPlusDistr

multPlusDistr :: SNat n -> SNat m -> SNat l -> n :* (m :+ l) :=: n :* m :+ n :* l
multPlusDistr SZ     _ _ = Refl
multPlusDistr (SS n) m l = 
  start (sS n %* (m %+ l))
    =~= n %* (m %+ l) %+ (m %+ l)
    === (n %* m) %+ (n %* l) %+ (m %+ l) `because` plusCongR (m %+ l) (multPlusDistr n m l)
    === (n %* m) %+ (n %* l) %+ (l %+ m) `because` plusCongL ((n %* m) %+ (n %* l)) (plusCommutative m l)
    === n %* m %+ (n %*l %+ (l %+ m))    `because` symmetry (plusAssociative (n %* m) (n %* l) (l %+ m))
    === n %* l %+ (l %+ m) %+ n %* m     `because` plusCommutative (n %* m) (n %*l %+ (l %+ m))
    === (n %* l %+ l) %+ m %+ n %* m     `because` plusCongR (n %* m) (plusAssociative (n %* l) l m)
    =~= (sS n %* l)   %+ m %+ n %* m
    === (sS n %* l)   %+ (m %+ (n %* m)) `because` symmetry (plusAssociative (sS n %* l) m (n %* m))
    === (sS n %* l)   %+ ((n %* m) %+ m) `because` plusCongL (sS n %* l) (plusCommutative m (n %* m))
    =~= (sS n %* l)   %+ (sS n %* m)
    === (sS n %* m)   %+ (sS n %* l)     `because` plusCommutative (sS n %* l) (sS n %* m)

plusMultDistr :: SNat n -> SNat m -> SNat l -> (n :+ m) :* l :=: n :* l :+ m :* l
plusMultDistr SZ _ _ = Refl
plusMultDistr (SS n) m l =
  start ((SS n %+ m) %* l)
    =~= sS (n %+ m) %* l
    =~= (n %+ m) %* l %+ l
    === n %* l  %+  m %* l  %+  l   `because` plusCongR l (plusMultDistr n m l)
    === m %* l  %+  n %* l  %+  l   `because` plusCongR l (plusCommutative (n %* l) (m %* l))
    === m %* l  %+ (n %* l  %+  l)  `because` symmetry (plusAssociative (m %* l) (n %*l) l)
    =~= m %* l  %+ (sS n %* l)
    === (sS n %* l)  %+  (m %* l)   `because` plusCommutative (m %* l) (sS n %* l)

multAssociative :: SNat n -> SNat m -> SNat l -> n :* (m :* l) :=: (n :* m) :* l
multAssociative SZ     _ _ = Refl
multAssociative (SS n) m l =
  start (sS n %* (m %* l))
    =~= n %* (m %* l) %+ (m %* l)
    === (n %* m) %* l %+ (m %* l) `because` plusCongR (m %* l) (multAssociative n m l)
    === (n %* m %+ m) %* l        `because` symmetry (plusMultDistr (n %* m) m l)
    =~= (sS n %* m) %* l

multZL :: SNat m -> Zero :* m :=: Zero
multZL _ = Refl

multZR :: SNat m -> m :* Zero :=: Zero
multZR SZ = Refl
multZR (SS n) =
  start (sS n %* sZ)
    =~= n %* sZ %+ sZ
    === sZ %+ sZ      `because` plusCongR sZ (multZR n)
    =~= sZ

multOneL :: SNat n -> One :* n :=: n
multOneL n =
  start (sOne %* n)
    =~= sZero %* n %+ n
    =~= sZero %:+ n
    =~= n

multOneR :: SNat n -> n :* One :=: n
multOneR SZ = Refl
multOneR (SS n) =
  start (sS n %* sOne)
    =~= n %* sOne %+ sOne
    === n %+ sOne         `because` plusCongR sOne (multOneR n)
    === sS n              `because` symmetry (sAndPlusOne n)

multCongL :: SNat n -> m :=: l -> n :* m :=: n :* l
multCongL _ Refl = Refl

multCongR :: SNat n -> m :=: l -> m :* n :=: l :* n
multCongR _ Refl = Refl

multComm :: SNat n -> SNat m -> n :* m :=: m :* n
multComm SZ m =
  start (sZ %* m)
    =~= sZ
    === m %* sZ `because` symmetry (multZR m)
multComm (SS n) m =
  start (sS n %* m)
    =~= n %* m %+ m
    === m %* n %+ m          `because` plusCongR m (multComm n m)
    === m %* n %+ m %* sOne  `because` plusCongL (m %* n) (symmetry $ multOneR m)
    === m %* (n %+ sOne)     `because` symmetry (multPlusDistr m n sOne)
    === m %* sS n            `because` multCongL m (symmetry $ sAndPlusOne n)


--------------------------------------------------
-- * Properties of 'Leq'
--------------------------------------------------

leqRefl :: SNat n -> Leq n n
leqRefl SZ = ZeroLeq sZ
leqRefl (SS n) = SuccLeqSucc $ leqRefl n

leqSucc :: SNat n -> Leq n (S n)
leqSucc SZ = ZeroLeq sOne
leqSucc (SS n) = SuccLeqSucc $ leqSucc n

leqTrans :: Leq n m -> Leq m l -> Leq n l
leqTrans (ZeroLeq _) leq = ZeroLeq $ leqRhs leq
leqTrans (SuccLeqSucc nLeqm) (SuccLeqSucc mLeql) = SuccLeqSucc $ leqTrans nLeqm mLeql
leqTrans _ _ = error "impossible!"

instance Preorder Leq where
  reflexivity = leqRefl
  transitivity = leqTrans

plusMonotone :: Leq n m -> Leq l k -> Leq (n :+: l) (m :+: k)
plusMonotone (ZeroLeq m) (ZeroLeq k) = ZeroLeq (m %+ k)
plusMonotone (ZeroLeq m) (SuccLeqSucc leq) =
  case plusSR m (leqRhs leq) of
    Refl -> SuccLeqSucc $ plusMonotone (ZeroLeq m) leq
plusMonotone (SuccLeqSucc leq) leq' = SuccLeqSucc $ plusMonotone leq leq'

plusLeqL :: SNat n -> SNat m -> Leq n (n :+: m)
plusLeqL SZ     m = ZeroLeq $ coerce (symmetry $ plusZL m) m
plusLeqL (SS n) m =
  start (sS n)
    =<= sS (n %+ m) `because` SuccLeqSucc (plusLeqL n m)
    =~= sS n %+ m

plusLeqR :: SNat n -> SNat m -> Leq m (n :+: m)
plusLeqR n m =
  case plusCommutative n m of
    Refl -> plusLeqL m n

minLeqL :: SNat n -> SNat m -> Leq (Min n m) n
minLeqL SZ m = case zAbsorbsMinL m of Refl -> ZeroLeq sZ
minLeqL n SZ = case zAbsorbsMinR n of Refl -> ZeroLeq n
minLeqL (SS n) (SS m) = SuccLeqSucc (minLeqL n m)

minLeqR :: SNat n -> SNat m -> Leq (Min n m) m
minLeqR n m = case minComm n m of Refl -> minLeqL m n

leqAnitsymmetric :: Leq n m -> Leq m n -> n :=: m
leqAnitsymmetric (ZeroLeq _) (ZeroLeq _) = Refl
leqAnitsymmetric (SuccLeqSucc leq1) (SuccLeqSucc leq2) = eqPreservesS $ leqAnitsymmetric leq1 leq2
leqAnitsymmetric _ _ = bugInGHC

maxLeqL :: SNat n -> SNat m -> Leq n (Max n m)
maxLeqL SZ m = ZeroLeq (sMax sZ m)
maxLeqL n SZ = case maxZR n of
                 Refl -> leqRefl n
maxLeqL (SS n) (SS m) = SuccLeqSucc $ maxLeqL n m

maxLeqR :: SNat n -> SNat m -> Leq m (Max n m)
maxLeqR n m = case maxComm n m of
                Refl -> maxLeqL m n

leqSnZAbsurd :: Leq (S n) Z -> a
leqSnZAbsurd _ = error "cannot be occured"

leqnZElim :: Leq n Z -> n :=: Z
leqnZElim (ZeroLeq SZ) = Refl

leqSnLeq :: Leq (S n) m -> Leq n m
leqSnLeq (SuccLeqSucc leq) =
  let n = leqLhs leq
      m = sS $ leqRhs leq
  in start n
       =<= sS n   `because` leqSucc n
       =<= m      `because` SuccLeqSucc leq

leqPred :: Leq (S n) (S m) -> Leq n m
leqPred (SuccLeqSucc leq) = leq

leqSnnAbsurd :: Leq (S n) n -> a
leqSnnAbsurd (SuccLeqSucc leq) =
  case leqLhs leq of
    SS _ -> leqSnnAbsurd leq
    _    -> bugInGHC "cannot be occured"
  
--------------------------------------------------
-- * Conversion functions.
--------------------------------------------------

-- | Convert integral numbers into 'Nat'
intToNat :: (Integral a, Ord a) => a -> Nat
intToNat 0 = Z
intToNat n
    | n < 0     = error "negative integer"
    | otherwise = S $ intToNat (n P.- 1)

-- | Convert 'Nat' into normal integers.
natToInt :: Integral n => Nat -> n
natToInt Z     = 0
natToInt (S n) = natToInt n P.+ 1

-- | Convert 'SNat n' into normal integers.
sNatToInt :: P.Num n => SNat x -> n
sNatToInt SZ     = 0
sNatToInt (SS n) = sNatToInt n P.+ 1

instance Monomorphicable (Sing :: Nat -> *) where
  type MonomorphicRep (Sing :: Nat -> *) = Int
  demote  (Monomorphic sn) = sNatToInt sn
  promote n
      | n < 0     = error "negative integer!"
      | n == 0    = Monomorphic sZ
      | otherwise = withPolymorhic (n P.- 1) $ \sn -> Monomorphic $ sS sn

--------------------------------------------------
-- * Quasi Quoter
--------------------------------------------------

-- | Quotesi-quoter for 'Nat'. This can be used for an expression, pattern and type.
--
--   for example: @sing :: SNat ([nat| 2 |] :+ [nat| 5 |])@
nat :: QuasiQuoter
nat = QuasiQuoter { quoteExp = P.foldr appE (conE 'Z) . P.flip P.replicate (conE 'S) . P.read
                  , quotePat = P.foldr (\a b -> conP a [b]) (conP 'Z []) . P.flip P.replicate 'S . P.read
                  , quoteType = P.foldr appT (conT 'Z) . P.flip P.replicate (conT 'S) . P.read
                  , quoteDec = error "not implemented"
                  }

-- | Quotesi-quoter for 'SNat'. This can be used for an expression, pattern and type.
-- 
--  For example: @[snat|12|] '%+' [snat| 5 |]@, @'sing' :: [snat| 12 |]@, @f [snat| 12 |] = \"hey\"@
snat :: QuasiQuoter
snat = QuasiQuoter { quoteExp = P.foldr appE (conE 'SZ) . P.flip P.replicate (conE 'SS) . P.read
                   , quotePat = P.foldr (\a b -> conP a [b]) (conP 'SZ []) . P.flip P.replicate 'SS . P.read
                   , quoteType = appT (conT ''SNat) . P.foldr appT (conT 'Z) . P.flip P.replicate (conT 'S) . P.read
                   , quoteDec = error "not implemented"
                   }
