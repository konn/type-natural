{-# LANGUAGE ConstraintKinds, CPP, DataKinds, GADTs, PolyKinds, RankNTypes #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances             #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Presburger #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
-- | Coercion between Peano Numerals @'Data.Type.Natural.Nat'@ and builtin naturals @'GHC.TypeLits.Nat'@
module Data.Type.Natural.Builtin
       ( -- * Sysnonym to avoid confusion
         Peano,
         -- * Coercion between builtin type-level natural and peano numerals
         FromPeano, ToPeano, sFromPeano, sToPeano,
         -- * Properties of @'FromPeano'@ and @'ToPeano'@.
         fromPeanoInjective, toPeanoInjective,
         -- ** Bijection
         fromToPeano, toFromPeano,
         -- ** Algebraic isomorphisms
         fromPeanoZeroCong, toPeanoZeroCong,
         fromPeanoOneCong,  toPeanoOneCong,
         fromPeanoSuccCong, toPeanoSuccCong,
         fromPeanoPlusCong, toPeanoPlusCong,
         fromPeanoMultCong, toPeanoMultCong,
         fromPeanoMonotone, toPeanoMonotone,
         -- * Peano and commutative ring axioms for built-in @'GHC.TypeLits.Nat'@
         plusZR, plusZL, plusSuccR, plusSuccL,
         multZR, multZL, multSuccR, multSuccL,
         inductionNat,
         plusComm, multComm, plusAssoc, multAssoc,
         plusMultDistr, multPlusDistr
       )
       where
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
import Data.Type.Natural.Compat
#endif

import Data.Promotion.Prelude.Enum (Succ)
import           Data.Singletons              (Sing, SingI, sing)
import           Data.Singletons.Decide       (Decision (..), (%~))
import           Data.Singletons.Decide       (Void)
import           Data.Singletons.Prelude.Bool (Sing (..))
import           Data.Singletons.Prelude.Ord  (POrd(..), SOrd ((%:<=)))
import           Data.Singletons.Prelude.Enum (Pred, sPred, sSucc)
import           Data.Singletons.Prelude.Num  (SNum (..))
import           Data.Type.Natural            (Nat (S, Z), Sing (SS, SZ))
import           Data.Type.Natural            (plusCongR)
import qualified Data.Type.Natural            as PN
import           Data.Void                    (absurd)
import qualified GHC.TypeLits                 as TL
import           Proof.Equational             ((:=:), (:~:) (Refl), coerce)
import           Proof.Equational             (start, sym, (===), (=~=))
import           Proof.Equational             (because)
import           Unsafe.Coerce                (unsafeCoerce)

-- | Type synonym for @'PN.Nat'@ to avoid confusion with built-in @'TL.Nat'@.
type Peano = PN.Nat

type family FromPeano (n :: PN.Nat) :: TL.Nat where
  FromPeano 'Z = 0
  FromPeano ('S n) = Succ (FromPeano n)

type family ToPeano (n :: TL.Nat) :: PN.Nat where
  ToPeano 0 = 'Z
  ToPeano n = 'S (ToPeano (Pred n))

data NatView (n :: TL.Nat) where
  IsZero :: NatView 0
  IsSucc :: Sing n -> NatView (Succ n)

viewNat :: Sing n -> NatView n
viewNat n =
  case n %~ (sing :: Sing 0) of
    Proved Refl -> IsZero
    Disproved _ -> IsSucc (sPred n)

sFromPeano :: Sing n -> Sing (FromPeano n)
sFromPeano SZ = sing
sFromPeano (SS sn) = sSucc (sFromPeano sn)

toPeanoInjective :: ToPeano n :=: ToPeano m -> n :=: m
toPeanoInjective Refl = Refl

-- trustMe :: a :=: b
-- trustMe = unsafeCoerce (Refl :: () :=: ())
-- {-# WARNING trustMe
--     "Used unproven type-equalities; This may cause disastrous result..." #-}

toPeanoSuccCong :: Sing n -> ToPeano (Succ n) :=: 'S (ToPeano n)
toPeanoSuccCong _ = unsafeCoerce (Refl :: () :=: ())
  -- We cannot prove this lemma within Haskell, so we assume it a priori.

sToPeano :: Sing n -> Sing (ToPeano n)
sToPeano sn =
  case sn %~ (sing :: Sing 0) of
    Proved Refl  -> SZ
    Disproved _pf -> coerce (sym (toPeanoSuccCong (sPred sn))) (SS (sToPeano (sPred sn)))

-- litSuccInjective :: forall (n :: TL.Nat) (m :: TL.Nat).
--                     Succ n :=: Succ m -> n :=: m
-- litSuccInjective Refl = Refl

toFromPeano :: Sing n -> ToPeano (FromPeano n) :=: n
toFromPeano SZ = Refl
toFromPeano (SS sn) =
  start (sToPeano (sFromPeano (SS sn)))
    =~= sToPeano (sSucc (sFromPeano sn))
    === SS (sToPeano (sFromPeano sn)) `because` toPeanoSuccCong (sFromPeano sn)
    === SS sn                         `because` PN.succCong (toFromPeano sn)

congFromPeano :: n :=: m -> FromPeano n :=: FromPeano m
congFromPeano Refl = Refl

congToPeano :: n :=: m -> ToPeano n :=: ToPeano m
congToPeano Refl = Refl

congSucc :: n :=: m -> Succ n :=: Succ m
congSucc Refl = Refl

fromToPeano :: Sing n -> FromPeano (ToPeano n) :=: n
fromToPeano sn  =
  case viewNat sn of
    IsZero    -> Refl
    IsSucc n1 ->
      start (sFromPeano (sToPeano sn))
        =~= sFromPeano (sToPeano (sSucc n1))
        === sFromPeano (SS (sToPeano n1))
              `because` congFromPeano (toPeanoSuccCong n1)
        =~= sSucc (sFromPeano (sToPeano n1))
        === sSucc n1 `because` congSucc (fromToPeano n1)

fromPeanoInjective :: forall n m. (SingI n, SingI m)
                   => FromPeano n :=: FromPeano m -> n :=: m
fromPeanoInjective frEq =
  let sn = sing :: Sing n
      sm = sing :: Sing m
  in start sn
       === sToPeano (sFromPeano sn) `because` sym (toFromPeano sn)
       === sToPeano (sFromPeano sm) `because` congToPeano frEq
       === sm                       `because` toFromPeano sm

fromPeanoSuccCong :: Sing n -> FromPeano ('S n) :=: Succ (FromPeano n)
fromPeanoSuccCong _sn = Refl

fromPeanoPlusCong :: Sing n -> Sing m -> FromPeano (n PN.:+ m) :=: FromPeano n TL.+ FromPeano m
fromPeanoPlusCong SZ _ = Refl
fromPeanoPlusCong (SS sn) sm =
  start (sFromPeano (SS sn %:+ sm))
    =~= sFromPeano (SS (sn %:+ sm))
    === sSucc (sFromPeano (sn %:+ sm))           `because` fromPeanoSuccCong (sn %:+ sm)
    === sSucc (sFromPeano sn  %:+ sFromPeano sm) `because` congSucc (fromPeanoPlusCong sn sm)
    =~= sSucc (sFromPeano sn) %:+ sFromPeano sm
    =~= sFromPeano (SS sn)    %:+ sFromPeano sm

toPeanoPlusCong :: Sing n -> Sing m -> ToPeano (n TL.+ m) :=: ToPeano n PN.:+ ToPeano m
toPeanoPlusCong sn sm =
  case viewNat sn of
    IsZero -> Refl
    IsSucc pn ->
      start (sToPeano (sSucc pn %:+ sm))
        =~= sToPeano (sSucc (pn %:+ sm))
        === SS (sToPeano (pn %:+ sm))
            `because` toPeanoSuccCong (pn %:+ sm)
        === SS (sToPeano pn %:+ sToPeano sm)
            `because` PN.succCong (toPeanoPlusCong pn sm)
        =~= SS (sToPeano pn) %:+ sToPeano sm
        === (sToPeano (sSucc pn) %:+ sToPeano sm)
            `because` plusCongR (sToPeano sm) (sym (toPeanoSuccCong pn))
        =~= sToPeano sn %:+ sToPeano sm

fromPeanoZeroCong :: FromPeano 'Z :=: 0
fromPeanoZeroCong = Refl

toPeanoZeroCong :: ToPeano 0 :=: 'Z
toPeanoZeroCong = Refl

fromPeanoOneCong :: FromPeano PN.One :=: 1
fromPeanoOneCong = Refl

toPeanoOneCong :: ToPeano 1 :=: PN.One
toPeanoOneCong = Refl

natPlusCongR :: Sing r -> n :=: m -> n TL.+ r :=: m TL.+ r
natPlusCongR _ Refl = Refl

fromPeanoMultCong :: Sing n -> Sing m -> FromPeano (n PN.:* m) :=: FromPeano n TL.* FromPeano m
fromPeanoMultCong SZ _ = Refl
fromPeanoMultCong (SS psn) sm =
  start (sFromPeano (SS psn %:* sm))
    =~= sFromPeano (psn %:* sm %:+ sm)
    === sFromPeano (psn %:* sm) %:+ sFromPeano sm
        `because` fromPeanoPlusCong (psn %:* sm) sm
    === sFromPeano psn %:* sFromPeano sm %:+ sFromPeano sm
        `because` natPlusCongR (sFromPeano sm) (fromPeanoMultCong psn sm)
    =~= sSucc (sFromPeano psn) %:* sFromPeano sm
    =~= sFromPeano (SS psn)    %:* sFromPeano sm


toPeanoMultCong :: Sing n -> Sing m -> ToPeano (n PN.:* m) :=: ToPeano n PN.:* ToPeano m
toPeanoMultCong sn sm =
  case viewNat sn of
    IsZero -> Refl
    IsSucc psn ->
      start (sToPeano (sSucc psn %:* sm))
        =~= sToPeano (psn %:* sm %:+ sm)
        === sToPeano (psn %:* sm) %:+ sToPeano sm
            `because` toPeanoPlusCong (psn %:* sm) sm
        === sToPeano psn %:* sToPeano sm %:+ sToPeano sm
            `because` plusCongR (sToPeano sm) (toPeanoMultCong psn sm)
        =~= SS (sToPeano psn) %:* sToPeano sm
        === sToPeano (sSucc psn) %:* sToPeano sm
            `because` PN.multCongR (sToPeano sm) (sym (toPeanoSuccCong psn))

infix 4 %:<=?
(%:<=?) :: Sing n -> Sing m -> Sing (n TL.<=? m)
sn %:<=? sm =
  case viewNat sn of
    IsZero -> STrue
    IsSucc pn -> case viewNat sm of
      IsZero -> SFalse
      IsSucc pm ->
        case pn %:<=? pm of
          STrue  -> STrue
          SFalse -> SFalse

natLeqSuccEq :: Sing n -> Sing m -> ((n TL.+ 1) TL.<=? (m TL.+ 1)) :~: (n TL.<=? m)
natLeqSuccEq _ _ = Refl

leqqCong :: n :=: m -> l :=: z -> (n TL.<=? l) :~: (m TL.<=? z)
leqqCong Refl Refl = Refl

leqCong :: n :=: m -> l :=: z -> (n :<= l) :~: (m :<= z)
leqCong Refl Refl = Refl

fromPeanoMonotone :: ((n :<= m) ~ 'True) => Sing n -> Sing m -> (FromPeano n TL.<=? FromPeano m) :=: 'True
fromPeanoMonotone SZ _ = Refl
fromPeanoMonotone (SS n) (SS m) =
   start (sFromPeano (SS n) %:<=? sFromPeano (SS m))
     === (sSucc (sFromPeano n) %:<=? sSucc (sFromPeano m))
      `because` leqqCong  (fromPeanoSuccCong n) (fromPeanoSuccCong m)
     === (sFromPeano n %:<=? sFromPeano m)
      `because` natLeqSuccEq (sFromPeano n) (sFromPeano m)
     === STrue
      `because` fromPeanoMonotone n m
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 800
fromPeanoMonotone _ _ = bugInGHC
#endif

natLeqZero :: (n TL.<= 0) => Sing n -> n :~: 0
natLeqZero _ = Refl

-- | Currently, ghc-typelits-natnormalise reduces @(0 - 1) + 1@ to @0@,
--   which is contradictory to current GHC's behaviour.
--   So our assumption @((n :~: 0) -> Void)@ is simply disregarded.
natSuccPred :: ((n :~: 0) -> Void) -> Succ (Pred n) :=: n
natSuccPred _ = Refl

myLeqPred :: Sing n -> Sing m -> ('S n :<= 'S m) :=: (n :<= m)
myLeqPred SZ _ = Refl
myLeqPred (SS _) (SS _) = Refl
myLeqPred (SS _) SZ = Refl

toPeanoCong :: a :=: b -> ToPeano a :=: ToPeano b
toPeanoCong Refl = Refl

toPeanoMonotone :: (n TL.<= m)
                => Sing n -> Sing m -> ((ToPeano n) :<= (ToPeano m)) :~: 'True
toPeanoMonotone sn sm =
  case sn %~ (sing :: Sing 0) of
    Proved Refl -> Refl
    Disproved nPos -> case sm %~ (sing :: Sing 0) of
      Proved Refl -> absurd $ nPos $ natLeqZero sm
      Disproved mPos ->
        let pn = sPred sn
            pm = sPred sm
        in start (sToPeano sn %:<= sToPeano sm)
             === (sToPeano (sSucc pn) %:<= sToPeano (sSucc pm))
                 `because` leqCong (toPeanoCong $ sym $ natSuccPred nPos)
                                   (toPeanoCong $ sym $ natSuccPred mPos)
             === (SS (sToPeano pn) %:<= SS (sToPeano pm))
                 `because` leqCong (toPeanoSuccCong pn) (toPeanoSuccCong pm)
             === (sToPeano pn %:<= sToPeano pm)
                 `because` myLeqPred (sToPeano pn) (sToPeano pm)
             === STrue `because` toPeanoMonotone pn pm

-- | Induction scheme for built-in @'TL.Nat'@.
inductionNat :: forall p n. p 0 -> (forall m. p m -> p (m TL.+ 1)) -> Sing n -> p n
inductionNat base step snat =
  case viewNat snat of
    IsZero -> base
    IsSucc sl -> step (inductionNat base step sl)

plusZR :: Sing n -> n TL.+ 0 :~: n
plusZR _ = Refl

plusZL :: Sing n -> 0 TL.+ n :~: n
plusZL _ = Refl

plusSuccL :: Sing n -> Sing m -> (Succ n) TL.+ m :~: Succ (n TL.+ m)
plusSuccL _ _ =  Refl

plusSuccR :: Sing n -> Sing m -> n TL.+ (Succ m) :~: Succ (n TL.+ m)
plusSuccR _ _ =  Refl

multZL :: Sing n -> 0 TL.* n :~: 0
multZL _ = Refl

multZR :: Sing n -> n TL.* 0 :~: 0
multZR _ = Refl

multSuccL :: Sing n -> Sing m -> Succ n TL.* m :~: (n TL.* m) TL.+ m
multSuccL _ _ = Refl

multSuccR :: Sing n -> Sing m -> n TL.* Succ m :~: (n TL.* m) TL.+ n
multSuccR _ _ = Refl

plusComm :: Sing n -> Sing m -> (n TL.+ m) :~: (m TL.+ n)
plusComm _ _ = Refl

multComm :: Sing n -> Sing m -> (n TL.* m) :~: (m TL.* n)
multComm _ _ = Refl

plusAssoc :: Sing n -> Sing m -> Sing l -> (n TL.+ m) TL.+ l :~: n TL.+ (m TL.+ l)
plusAssoc _ _ _ = Refl

multAssoc :: Sing n -> Sing m -> Sing l -> (n TL.* m) TL.* l :~: n TL.* (m TL.* l)
multAssoc _ _ _ = Refl

plusMultDistr :: Sing n -> Sing m -> Sing l -> (n TL.+ m) TL.* l :~: n TL.* l TL.+  m TL.* l
plusMultDistr _ _ _ = Refl

multPlusDistr :: Sing n -> Sing m -> Sing l -> n TL.* (m TL.+ l) :~: n TL.* m TL.+  n TL.* l
multPlusDistr _ _ _ = Refl
