{-# LANGUAGE DataKinds, ExplicitForAll, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, KindSignatures, MultiParamTypeClasses, PolyKinds        #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeFamilies, TypeInType      #-}
module Data.Type.Natural.Class (Zero, One, S, ZeroOrSucc(..),
                                plusCong, plusCongR, plusCongL, succCong,
                                multCong, multCongL, multCongR,
                                minusCong, minusCongL, minusCongR,
                                IsPeano(..), PeanoOrder(..), DiffNat(..), LeqView(..)) where
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Type.Equality
import Data.Void
import Proof.Equational
import Proof.Propositional

type family Zero k :: k where
  Zero k = FromInteger 0

sZero :: SNum nat => Sing (Zero nat)
sZero = sFromInteger (sing :: Sing 0)

type family One k :: k where
  One k = FromInteger 1

sOne :: SNum nat => Sing (One nat)
sOne = sFromInteger (sing :: Sing 1)

type S n = Succ n

sS :: SEnum nat => Sing (n :: nat) -> Sing (S n)
sS = sSucc

predCong :: n :~: m -> Pred n :~: Pred m
predCong Refl = Refl

plusCong :: n :~: m -> n' :~: m' -> n :+ n' :~: m :+ m'
plusCong Refl Refl = Refl

plusCongL :: n :~: m -> Sing k -> n :+ k :~: m :+ k
plusCongL Refl _ = Refl

plusCongR :: Sing k -> n :~: m -> k :+ n :~: k :+ m
plusCongR _ Refl = Refl

succCong :: n :~: m -> S n :~: S m
succCong Refl = Refl

multCong :: n :~: m -> l :~: k -> n :* l :~: m :* k
multCong Refl Refl = Refl

multCongL :: n :~: m -> Sing k -> n :* k :~: m :* k
multCongL Refl _ = Refl

multCongR :: Sing k -> n :~: m -> k :* n :~: k :* m
multCongR _ Refl = Refl

minusCong :: n :~: m -> l :~: k -> n :- l :~: m :- k
minusCong Refl Refl = Refl

minusCongL :: n :~: m -> Sing k -> n :- k :~: m :- k
minusCongL Refl _ = Refl

minusCongR :: Sing k -> n :~: m -> k :- n :~: k :- m
minusCongR _ Refl = Refl

data ZeroOrSucc (n :: nat) where
  IsZero :: ZeroOrSucc (Zero n)
  IsSucc :: Sing n -> ZeroOrSucc (Succ n)

newtype Assoc op n = Assoc { assocProof :: forall k l. Sing k -> Sing l ->
                             Apply (op (Apply (op n) k)) l :~:
                             Apply (op n) (Apply (op k) l)
                           }


newtype IdentityR op e (n :: nat) = IdentityR { idRProof :: Apply (op n) e :~: n }
newtype IdentityL op e (n :: nat) = IdentityL { idLProof :: Apply (op e) n :~: n }

type PlusZeroR (n :: nat) = IdentityR (:+$$) (Zero nat) n
newtype PlusSuccR (n :: nat) =
  PlusSuccR { plusSuccRProof :: forall m. Sing m -> n :+ S m :~: S (n :+ m) }

type PlusZeroL (n :: nat) = IdentityL (:+$$) (Zero nat) n
newtype PlusSuccL (m :: nat) =
  PlusSuccL { plusSuccLProof :: forall n. Sing n -> S n :+ m :~: S (n :+ m) }

newtype Comm op n = Comm { commProof :: forall m. Sing m -> Apply (op n) m :~: Apply (op m) n }

type PlusComm = Comm (:+$$)

newtype MultZeroL (n :: nat) = MultZeroL { multZeroLProof :: Zero nat :* n :~: Zero nat }
newtype MultZeroR (n :: nat) = MultZeroR { multZeroRProof :: n :* Zero nat :~: Zero nat }

newtype MultSuccL (m :: nat) = MultSuccL { multSuccLProof :: forall n. Sing n -> S n :* m :~: n :* m :+ m }
newtype MultSuccR (n :: nat) = MultSuccR { multSuccRProof :: forall m. Sing m -> n :* S m :~: n :* m :+ n }

newtype PlusMultDistrib n =
  PlusMultDistrib { plusMultDistribProof :: forall m l. Sing m -> Sing l
                                         -> (n :+ m) :* l :~: n :* l :+ m :* l
                  }

newtype PlusEqCancelL n = PlusEqCancelL { plusEqCancelLProof :: forall m l . Sing m -> Sing l
                                                       -> n :+ m :~: n :+ l -> m :~: l }

newtype SuccPlusL (n :: nat) = SuccPlusL { proofSuccPlusL :: Succ n :~: One nat :+ n }
newtype MultEqCancelR n =
  MultEqCancelR { proofMultEqCancelR :: forall m l. Sing m -> Sing l
                                        -> n :* Succ l :~: m :* Succ l
                                        -> n :~: m
                }

class (SNum nat, SEnum nat) => IsPeano nat where
  {-# MINIMAL succOneCong, succNonCyclic, predSucc, plusMinus,
              succInj, ( (plusZeroL, plusSuccL) | (plusZeroR, plusZeroL))
                     , ( (multZeroL, multSuccL) | (multZeroR, multSuccR)),
              induction #-}

  succOneCong   :: Succ (Zero nat) :~: One nat
  succInj       :: Succ n :~: Succ (m :: nat) -> n :~: m
  succNonCyclic :: Sing n -> Succ n :~: Zero nat -> Void
  induction     :: p (Zero nat) -> (forall n. Sing n -> p n -> p (S n)) -> Sing k -> p k
  plusMinus :: Sing (n :: nat) -> Sing m -> n :+ m :- m :~: n


  plusZeroL :: Sing n -> (Zero nat :+ n) :~: n
  plusZeroL sn = idLProof (induction base step sn)
    where
      base :: PlusZeroL (Zero nat)
      base = IdentityL (plusZeroR sZero)

      step :: Sing (n :: nat) -> PlusZeroL n -> PlusZeroL (S n)
      step sk (IdentityL ih) = IdentityL $
        start (sZero %:+ sS sk)
          === sS (sZero %:+ sk) `because` plusSuccR sZero sk
          === sS sk             `because` succCong ih

  plusSuccL :: Sing n -> Sing m -> S n :+ m :~: S (n :+ m :: nat)
  plusSuccL sn0 sm0 = plusSuccLProof (induction base step sm0) sn0
    where
      base :: PlusSuccL (Zero nat)
      base = PlusSuccL $ \sn ->
        start (sS sn %:+ sZero)
          === sS sn             `because` plusZeroR (sS sn)
          === sS (sn %:+ sZero) `because` succCong (sym $ plusZeroR sn)

      step :: Sing (n :: nat) -> PlusSuccL n -> PlusSuccL (S n)
      step sm (PlusSuccL ih) = PlusSuccL $ \sn ->
        start (sS sn %:+ sS sm)
        === sS (sS sn %:+ sm)   `because` plusSuccR (sS sn) sm
        === sS (sS (sn %:+ sm)) `because` succCong (ih sn)
        === sS (sn %:+ sS sm)   `because` succCong (sym $ plusSuccR sn sm)

  plusZeroR :: Sing n -> (n :+ Zero nat) :~: n
  plusZeroR sn = idRProof (induction base step sn)
    where
      base :: PlusZeroR (Zero nat)
      base = IdentityR (plusZeroL sZero)

      step :: Sing (n :: nat) -> PlusZeroR n -> PlusZeroR (S n)
      step sk (IdentityR ih) = IdentityR $
        start (sS sk %:+ sZero)
          === sS (sk %:+ sZero) `because` plusSuccL sk sZero
          === sS sk             `because` succCong ih

  plusSuccR :: Sing n -> Sing m -> n :+ S m :~: S (n :+ m :: nat)
  plusSuccR sn0 = plusSuccRProof (induction base step sn0)
    where
      base :: PlusSuccR (Zero nat)
      base = PlusSuccR $ \sk ->
        start (sZero %:+ sS sk)
          === sS sk             `because` plusZeroL (sS sk)
          === sS (sZero %:+ sk) `because` succCong (sym $ plusZeroL sk)

      step :: Sing (n :: nat) -> PlusSuccR n -> PlusSuccR (S n)
      step sn (PlusSuccR ih) = PlusSuccR $ \sk ->
        start (sS sn %:+ sS sk)
        === sS (sn %:+ sS sk)    `because` plusSuccL sn (sS sk)
        === sS (sS (sn %:+ sk))  `because` succCong (ih sk)
        === sS (sS sn %:+ sk)    `because` succCong (sym $ plusSuccL sn sk)

  plusComm  :: Sing n -> Sing m -> n :+ m :~: (m :: nat) :+ n
  plusComm sn0 = commProof (induction base step sn0)
    where
      base :: PlusComm (Zero nat)
      base = Comm $ \sk ->
        start (sZero %:+ sk)
          === sk             `because` plusZeroL sk
          === (sk %:+ sZero) `because` sym (plusZeroR sk)

      step :: Sing (n :: nat) -> PlusComm n -> PlusComm (S n)
      step sn (Comm ih) = Comm $ \sk ->
        start (sS sn %:+ sk)
          === sS (sn %:+ sk) `because` plusSuccL sn sk
          === sS (sk %:+ sn) `because` succCong (ih sk)
          === sk %:+ sS sn   `because` sym (plusSuccR sk sn)

  plusAssoc :: forall n m l. Sing (n :: nat) -> Sing m -> Sing l
            -> (n :+ m) :+ l :~: n :+ (m :+ l)
  plusAssoc sn m l = assocProof (induction base step sn) m l
    where
      base :: Assoc (:+$$) (Zero nat)
      base = Assoc $ \ sk sl ->
        start ((sZero %:+ sk) %:+ sl)
          === sk %:+ sl
              `because` plusCongL (plusZeroL sk) sl
          === (sZero %:+ (sk %:+ sl))
              `because` sym (plusZeroL (sk %:+ sl))

      step :: forall k . Sing (k :: nat) -> Assoc (:+$$) k -> Assoc (:+$$) (S k)
      step sk (Assoc ih) = Assoc $ \ sl su ->
        start ((sS sk %:+ sl) %:+ su)
        ===   (sS (sk %:+ sl) %:+ su) `because` plusCongL (plusSuccL sk sl) su
        ===   sS (sk %:+ sl %:+ su)   `because` plusSuccL (sk %:+ sl) su
        ===   sS (sk %:+ (sl %:+ su)) `because` succCong (ih sl su)
        ===   sS sk %:+ (sl %:+ su)   `because` sym (plusSuccL sk (sl %:+ su))


  multZeroL :: Sing n -> Zero nat :* n :~: Zero nat
  multZeroL sn0 = multZeroLProof $ induction base step sn0
    where
      base :: MultZeroL (Zero nat)
      base = MultZeroL (multZeroR sZero)

      step :: Sing (k :: nat) -> MultZeroL k ->  MultZeroL (S k)
      step sk (MultZeroL ih) = MultZeroL $
        start (sZero %:* sS sk)
        === sZero %:* sk %:+ sZero  `because` multSuccR sZero sk
        === sZero %:* sk            `because` plusZeroR (sZero %:* sk)
        === sZero                   `because` ih

  multSuccL :: Sing (n :: nat) -> Sing m -> S n :* m :~: n :* m :+ m
  multSuccL sn0 sm0 = multSuccLProof (induction base step sm0) sn0
    where
      base :: MultSuccL (Zero nat)
      base = MultSuccL $ \sk ->
        start (sS sk %:* sZero)
          === sZero                  `because` multZeroR (sS sk)
          === sk %:* sZero           `because` sym (multZeroR sk)
          === sk %:* sZero %:+ sZero `because` sym (plusZeroR (sk %:* sZero))

      step :: Sing (m :: nat) -> MultSuccL m -> MultSuccL (S m)
      step sm (MultSuccL ih) = MultSuccL $ \sk ->
        start (sS sk %:* sS sm)
          === sS sk %:* sm       %:+ sS sk
              `because` multSuccR (sS sk) sm
          === (sk %:* sm %:+ sm) %:+ sS sk
              `because` plusCongL (ih sk) (sS sk)
          === sS ((sk %:* sm %:+ sm) %:+ sk)
              `because` plusSuccR (sk %:* sm %:+ sm) sk
          === sS (sk %:* sm %:+ (sm %:+ sk))
              `because` succCong (plusAssoc (sk %:* sm) sm sk)
          === sS (sk %:* sm %:+ (sk %:+ sm))
              `because` succCong (plusCongR (sk %:* sm) (plusComm sm sk))
          === sS ((sk %:* sm %:+ sk) %:+ sm)
              `because` succCong (sym $ plusAssoc (sk %:* sm) sk sm)
          === sS ((sk %:* sS sm) %:+ sm)
              `because` succCong (plusCongL (sym $ multSuccR sk sm) sm)
          === sk %:* sS sm %:+ sS sm `because` sym (plusSuccR (sk %:* sS sm) sm)

  multZeroR :: Sing n -> n :* Zero nat :~: Zero nat
  multZeroR sn0 = multZeroRProof $ induction base step sn0
    where
      base :: MultZeroR (Zero nat)
      base = MultZeroR (multZeroR sZero)

      step :: Sing (k :: nat) -> MultZeroR k ->  MultZeroR (S k)
      step sk (MultZeroR ih) = MultZeroR $
        start (sS sk %:* sZero)
        === sk %:* sZero %:+ sZero  `because` multSuccL sk sZero
        === sk %:* sZero            `because` plusZeroR (sk %:* sZero)
        === sZero                   `because` ih

  multSuccR :: Sing n -> Sing m -> n :* S m :~: n :* m :+ (n :: nat)
  multSuccR sn0 = multSuccRProof $ induction base step sn0
    where
      base :: MultSuccR (Zero nat)
      base = MultSuccR $ \sk ->
        start (sZero %:* sS sk)
          === sZero
              `because` multZeroL (sS sk)
          === sZero %:* sk
              `because` sym (multZeroL sk)
          === sZero %:* sk %:+ sZero
              `because` sym (plusZeroR (sZero %:* sk))


      step :: Sing (n :: nat) -> MultSuccR n -> MultSuccR (S n)
      step sn (MultSuccR ih) = MultSuccR $ \sk ->
        start (sS sn %:* sS sk)
          === sn %:* sS sk %:+ sS sk
              `because` multSuccL sn (sS sk)
          === sS (sn %:* sS sk %:+ sk)
              `because` plusSuccR (sn %:* sS sk) sk
          === sS (sn %:* sk %:+ sn %:+ sk)
              `because` succCong (plusCongL (ih sk) sk)
          === sS (sn %:* sk %:+ (sn %:+ sk))
              `because` succCong (plusAssoc (sn %:* sk) sn sk)
          === sS (sn %:* sk %:+ (sk %:+ sn))
              `because` succCong (plusCongR (sn %:* sk) (plusComm sn sk))
          === sS (sn %:* sk %:+ sk %:+ sn)
              `because` succCong (sym $ plusAssoc (sn %:* sk) sk sn)
          === sS (sS sn %:* sk %:+ sn)
              `because` succCong (plusCongL (sym $ multSuccL sn sk) sn)
          === sS sn %:* sk %:+ sS sn
              `because` sym (plusSuccR (sS sn %:* sk) sn)


  multComm  :: Sing (n :: nat) -> Sing m -> n :* m :~: m :* n
  multComm sn0 = commProof (induction base step sn0)
    where
      base :: Comm (:*$$) (Zero nat)
      base = Comm $ \sk ->
        start (sZero %:* sk)
          === sZero           `because` multZeroL sk
          === sk %:* sZero    `because` sym (multZeroR sk)

      step :: Sing (n :: nat) -> Comm (:*$$) n -> Comm (:*$$) (S n)
      step sn (Comm ih) = Comm $ \sk ->
        start (sS sn %:* sk)
          === sn %:* sk %:+ sk `because` multSuccL sn sk
          === sk %:* sn %:+ sk `because` plusCongL (ih sk) sk
          === sk %:* sS sn     `because` sym (multSuccR sk sn)

  multOneR :: Sing n -> n :* One nat :~: n
  multOneR sn =
    start (sn %:* sOne)
      === sn %:* sS sZero      `because` multCongR sn (sym $ succOneCong)
      === sn %:* sZero %:+ sn  `because` multSuccR sn sZero
      === sZero %:+ sn         `because` plusCongL (multZeroR sn) sn
      === sn                   `because` plusZeroL sn

  multOneL :: Sing n -> One nat :* n :~: n
  multOneL sn =
    start (sOne %:* sn)
      === sn %:* sOne   `because` multComm sOne sn
      === sn            `because` multOneR sn

  plusMultDistrib :: Sing (n :: nat) -> Sing m -> Sing l
                -> (n :+ m) :* l :~: n :* l :+ m :* l
  plusMultDistrib sn0 = plusMultDistribProof $ induction base step sn0
    where
      base :: PlusMultDistrib (Zero nat)
      base = PlusMultDistrib $ \sk sl ->
        start ((sZero %:+ sk) %:* sl)
          === (sk %:* sl)
              `because` multCongL (plusZeroL sk) sl
          === sZero %:+ (sk %:* sl)
              `because` sym (plusZeroL (sk %:* sl))
          === sZero %:* sl %:+ sk %:* sl
              `because` plusCongL (sym $ multZeroL sl) (sk %:* sl)

      step :: Sing (n :: nat) -> PlusMultDistrib n -> PlusMultDistrib (S n)
      step sn (PlusMultDistrib ih) = PlusMultDistrib $ \sk sl ->
        start ((sS sn %:+ sk) %:* sl)
          === (sS (sn %:+ sk) %:* sl)           `because` multCongL (plusSuccL sn sk) sl
          === (sn %:+ sk) %:* sl %:+ sl         `because` multSuccL (sn %:+ sk) sl
          === (sn %:* sl %:+ sk %:* sl) %:+ sl  `because` plusCongL (ih sk sl) sl
          === sn %:* sl %:+ (sk %:* sl %:+ sl)  `because` plusAssoc (sn %:* sl) (sk %:* sl) sl
          === sn %:* sl %:+ (sl %:+ sk %:* sl)  `because` plusCongR (sn %:* sl) (plusComm (sk %:* sl) sl)
          === (sn %:* sl %:+ sl) %:+ sk %:* sl  `because` sym (plusAssoc (sn %:* sl) sl (sk %:* sl))
          === (sS sn %:* sl) %:+ sk %:* sl      `because` plusCongL (sym $ multSuccL sn sl) (sk %:* sl)

  multPlusDistrib :: Sing (n :: nat) -> Sing m -> Sing l
                -> n :* (m :+ l) :~: n :* m :+ n :* l
  multPlusDistrib n m l =
    start (n %:* (m %:+ l))
      === (m %:+ l) %:* n     `because` multComm n (m %:+ l)
      === m %:* n %:+ l %:* n `because` plusMultDistrib m l n
      === n %:* m %:+ n %:* l `because` plusCong (multComm m n) (multComm l n)

  minusNilpotent :: Sing n -> n :- n :~: Zero nat
  minusNilpotent n =
    start (n %:- n)
      === (sZero %:+ n) %:- n  `because` minusCongL (sym $ plusZeroL n) n
      === sZero                `because` plusMinus sZero n


  multAssoc :: Sing (n :: nat) -> Sing m -> Sing l
            -> (n :* m) :* l :~: n :* (m :* l)
  multAssoc sn0 = assocProof $ induction base step sn0
    where
      base :: Assoc (:*$$) (Zero nat)
      base = Assoc $ \ m l ->
        start (sZero %:* m %:* l)
          === sZero %:* l  `because` multCongL (multZeroL m) l
          === sZero        `because` multZeroL l
          === sZero %:*  (m %:* l) `because` sym (multZeroL (m %:* l))

      step :: Sing (n :: nat) -> Assoc (:*$$) n -> Assoc (:*$$) (S n)
      step n _ = Assoc $ \ m l ->
        start (sS n %:* m %:* l)
          === (n %:* m %:+ m) %:* l        `because` multCongL (multSuccL n m) l
          === n %:* m %:* l %:+ m %:* l    `because` plusMultDistrib (n %:* m) m l
          === n %:* (m %:* l) %:+ m %:* l  `because` plusCongL (multAssoc n m l) (m %:* l)
          === sS n %:* (m %:* l)           `because` sym (multSuccL n (m %:* l))

  plusEqCancelL :: Sing (n :: nat) -> Sing m -> Sing l -> n :+ m :~: n :+ l -> m :~: l
  plusEqCancelL = plusEqCancelLProof . induction base step
    where
      base :: PlusEqCancelL (Zero nat)
      base = PlusEqCancelL $ \l m nlnm ->
        start l === sZero %:+ l `because` sym (plusZeroL l)
                === sZero %:+ m `because` nlnm
                === m           `because` plusZeroL m

      step :: Sing (n :: nat) -> PlusEqCancelL n -> PlusEqCancelL (Succ n)
      step n (PlusEqCancelL ih) = PlusEqCancelL $ \l m snlsnm ->
        succInj $ ih (sS l) (sS m) $
          start (n %:+ sS l)
            ===  sS (n %:+ l)  `because` plusSuccR n l
            ===  sS n %:+ l    `because` sym (plusSuccL n l)
            ===  sS n %:+ m    `because` snlsnm
            ===  sS (n %:+ m)  `because` plusSuccL n m
            ===  n %:+ sS m    `because` sym (plusSuccR n m)

  plusEqCancelR :: forall n m l . Sing (n :: nat) -> Sing m -> Sing l -> n :+ l :~: m :+ l -> n :~: m
  plusEqCancelR n m l nlml = plusEqCancelL l n m $
    start (l %:+ n)
      === (n %:+ l) `because` plusComm l n
      === (m %:+ l) `because` nlml
      === (l %:+ m) `because` plusComm m l

  succAndPlusOneL :: Sing n -> Succ n :~: One nat :+ n
  succAndPlusOneL = proofSuccPlusL . induction base step
    where
      base :: SuccPlusL (Zero nat)
      base = SuccPlusL $
             start (sSucc sZero)
               === sOne           `because` succOneCong
               === sOne %:+ sZero `because` sym (plusZeroR sOne)

      step :: Sing (n :: nat) -> SuccPlusL n -> SuccPlusL (Succ n)
      step sn (SuccPlusL ih) = SuccPlusL $
        start (sSucc (sSucc sn))
          === sSucc (sOne %:+ sn) `because` succCong ih
          === sOne %:+ sSucc sn   `because` sym (plusSuccR sOne sn)

  succAndPlusOneR :: Sing n -> Succ n :~: n :+ One nat
  succAndPlusOneR n =
    start (sSucc n)
      === sOne %:+ n `because` succAndPlusOneL n
      === n %:+ sOne `because` plusComm sOne n

  predSucc :: Sing n -> Pred (Succ n) :~: (n :: nat)

  zeroOrSucc :: Sing (n :: nat) -> ZeroOrSucc n
  zeroOrSucc = induction base step
    where
      base = IsZero
      step sn _ = IsSucc sn

  plusEqZeroL :: Sing n -> Sing m -> n :+ m :~: Zero nat -> n :~: Zero nat
  plusEqZeroL n m Refl =
    case zeroOrSucc n of
      IsZero -> Refl
      IsSucc pn -> absurd $ succNonCyclic (pn %:+ m) (sym $ plusSuccL pn m)

  plusEqZeroR :: Sing n -> Sing m -> n :+ m :~: Zero nat -> m :~: Zero nat
  plusEqZeroR n m = plusEqZeroL m n . trans (plusComm m n)

  predUnique :: Sing (n :: nat) -> Sing m -> Succ n :~: m -> n :~: Pred m
  predUnique n m snEm =
    start n === (sPred (sSucc n)) `because` sym (predSucc n)
            === sPred m           `because` predCong snEm

  multEqSuccElimL :: Sing (n :: nat) -> Sing m -> Sing l -> n :* m :~: Succ l -> n :~: Succ (Pred n)
  multEqSuccElimL n m l nmEsl =
    case zeroOrSucc n of
      IsZero -> absurd $ succNonCyclic l $ sym $
                start sZero === sZero %:* m `because` sym (multZeroL m)
                            === sSucc l     `because` nmEsl
      IsSucc pn -> succCong (predUnique pn n Refl)

  multEqSuccElimR :: Sing (n :: nat) -> Sing m -> Sing l -> n :* m :~: Succ l -> m :~: Succ (Pred m)
  multEqSuccElimR n m l nmEsl =
    multEqSuccElimL m n l (multComm m n `trans` nmEsl)

  multEqCancelR :: Sing (n :: nat) -> Sing m -> Sing l -> n :* Succ l :~: m :* Succ l -> n :~: m
  multEqCancelR = proofMultEqCancelR . induction base step
    where
      base :: MultEqCancelR (Zero nat)
      base = MultEqCancelR $ \m l zslmsl ->
        sym $ plusEqZeroR (m %:* l) m $ sym $ start sZero
          === sZero %:* l            `because` sym (multZeroL l)
          === sZero %:* l %:+ sZero  `because` sym (plusZeroR (sZero %:* l))
          === sZero %:* sSucc l      `because` sym (multSuccR sZero l)
          === m     %:* sSucc l      `because` zslmsl
          === m %:* l %:+ m          `because` multSuccR m l

      step :: Sing (n :: nat) -> MultEqCancelR n -> MultEqCancelR (Succ n)
      step n (MultEqCancelR ih) = MultEqCancelR $ \m l snmssnl ->
        let m' = sPred m
            pf = start (m %:* sSucc l)
                   === sSucc n %:* sSucc l         `because` sym snmssnl
                   === n %:* sSucc l %:+ sSucc l   `because` multSuccL n (sSucc l)
                   === sSucc (n %:* sSucc l %:+ l) `because` plusSuccR (n %:* sSucc l) l
            sm'Em = multEqSuccElimL m (sSucc l) (n %:* sSucc l %:+ l) pf
            pf' = ih m' l $ plusEqCancelR (n %:* sSucc l) (m' %:* sSucc l) (sSucc l) $
                  start (n %:* sSucc l %:+ sSucc l)
                    === sSucc (n %:* sSucc l %:+ l)  `because` plusSuccR (n %:* sSucc l) l
                    === m %:* sSucc l                `because` sym pf
                    === sSucc m' %:* sSucc l         `because` multCongL sm'Em (sSucc l)
                    === (m' %:* sSucc l %:+ sSucc l) `because` multSuccL m' (sSucc l)
        in succCong pf' `trans` sym sm'Em

  succPred :: Sing n -> (n :~: Zero nat -> Void) -> Succ (Pred n) :~: n
  succPred n nonZero =
    case zeroOrSucc n of
      IsZero -> absurd $ nonZero Refl
      IsSucc n' -> sym $ succCong $ predUnique n' n Refl

  multEqCancelL :: Sing (n :: nat) -> Sing m -> Sing l -> Succ n :* m :~: Succ n :* l -> m :~: l
  multEqCancelL n m l snmEsnl =
    multEqCancelR m l n $
    multComm m (sSucc n) `trans` snmEsnl `trans` multComm (sSucc n) l

data LeqView (n :: nat) (m :: nat) where
  LeqZero :: Sing n -> LeqView (Zero nat) n
  LeqSucc :: Sing n -> Sing m -> IsTrue (n :<= m) -> LeqView (Succ n) (Succ m)

data DiffNat n m where
  DiffNat :: Sing n -> Sing m -> DiffNat n (n :+ m)

newtype LeqWitPf n = LeqWitPf { leqWitPf :: forall m. Sing m -> IsTrue (n :<= m) -> DiffNat n m }
newtype LeqStepPf n = LeqStepPf { leqStepPf :: forall m l. Sing m -> Sing l -> n :+ l :~: m -> IsTrue (n :<= m) }

succDiffNat :: IsPeano nat => Sing n -> Sing m -> DiffNat (n :: nat) m -> DiffNat (Succ n) (Succ m)
succDiffNat _ _ (DiffNat n m) = coerce (plusSuccL n m) $ DiffNat (sSucc n) m

coerceLeqL :: forall (n :: nat) m l . IsPeano nat => n :~: m -> Sing l
           -> IsTrue (n :<= l) -> IsTrue (m :<= l)
coerceLeqL Refl _ Witness = Witness

coerceLeqR :: forall (n :: nat) m l . IsPeano nat =>  Sing l -> n :~: m
           -> IsTrue (l :<= n) -> IsTrue (l :<= m)
coerceLeqR _ Refl Witness = Witness

class (SOrd nat, IsPeano nat) => PeanoOrder nat where
  {-# MINIMAL ((leqWitness, leqStep) | (leqZero , leqSucc , viewLeq)),
              minLeqL, minLeqR, minLargest, maxLeqL, maxLeqR, maxLeast #-}
  leqWitness :: Sing (n :: nat) -> Sing m -> IsTrue (n :<= m) -> DiffNat n m
  leqWitness = leqWitPf . induction base step
    where
      base :: LeqWitPf (Zero nat)
      base = LeqWitPf $ \sm _ -> coerce (plusZeroL sm) $ DiffNat sZero sm

      step :: Sing (n :: nat) -> LeqWitPf n -> LeqWitPf (Succ n)
      step (n :: Sing n) (LeqWitPf ih) = LeqWitPf $ \m snLEQm ->
        case viewLeq (sSucc n) m snLEQm of
          LeqZero _ -> absurd $ succNonCyclic n Refl
          LeqSucc (_ :: Sing n') pm nLEQpm ->
            succDiffNat n pm $ ih pm $ coerceLeqL (succInj Refl :: n' :~: n) pm nLEQpm

  leqStep :: Sing (n :: nat) -> Sing m -> Sing l -> n :+ l :~: m -> IsTrue (n :<= m)
  leqStep = leqStepPf . induction base step
    where
      base :: LeqStepPf (Zero nat)
      base = LeqStepPf $ \k _ _ -> leqZero k

      step :: Sing (n :: nat) -> LeqStepPf n -> LeqStepPf (Succ n)
      step n (LeqStepPf ih) =
        LeqStepPf $ \k l snPlEqk ->
        let kEQspk = start k
                       === sSucc n %:+ l   `because` sym snPlEqk
                       === sSucc (n %:+ l) `because` plusSuccL n l
            pk = n %:+ l
        in coerceLeqR (sSucc n) (sym kEQspk) $ leqSucc n pk $ ih pk l Refl

  leqZero :: Sing n -> IsTrue (Zero nat :<= n)
  leqZero sn = leqStep sZero sn sn (plusZeroL sn)

  leqSucc :: Sing (n :: nat) -> Sing m -> IsTrue (n :<= m) -> IsTrue (Succ n :<= Succ m)
  leqSucc n m nLEQm =
    case leqWitness n m nLEQm of
      DiffNat _ k ->
        leqStep (sSucc n) (sSucc m) k $
           start (sSucc n %:+ k)
             === sSucc (n %:+ k)   `because` plusSuccL n k
             =~= sSucc m

  viewLeq :: forall n m . Sing (n :: nat) -> Sing m -> IsTrue (n :<= m) -> LeqView n m
  viewLeq n m nLEQm =
    case zeroOrSucc n of
      IsZero -> LeqZero m
      IsSucc pn ->
        case leqWitness (sSucc pn) m nLEQm of
          DiffNat _ k -> -- n + k = sS (pn + k) = m
            let mEpnPk = start m
                           =~= sS pn %:+ k
                           === sS (pn %:+ k) `because` plusSuccL pn k
            in coerce (sym mEpnPk) $ LeqSucc pn (pn %:+ k) (leqStep pn (pn %:+ k) k Refl)

  leqRefl :: Sing (n :: nat) -> IsTrue (n :<= n)
  leqRefl sn = leqStep sn sn sZero (plusZeroR sn)

  leqTrans :: Sing (n :: nat) -> Sing m -> Sing l -> IsTrue (n :<= m) -> IsTrue (m :<= l) -> IsTrue (n :<= l)
  leqTrans n m k nLEm mLEk =
    case leqWitness n m nLEm of
      DiffNat _ mMn -> case leqWitness m k mLEk of
        DiffNat _ kMn -> leqStep n k (mMn %:+ kMn) (sym $ plusAssoc n mMn kMn)

  leqAntisymm :: Sing (n :: nat) -> Sing m -> IsTrue (n :<= m) -> IsTrue (m :<= n) -> n :~: m
  leqAntisymm n m nLEm mLEn =
    case (leqWitness n m nLEm, leqWitness m n mLEn) of
      (DiffNat _ mMn, DiffNat _ nMm) ->
        let pEQ0 = plusEqCancelL n (mMn %:+ nMm) sZero $
                   start (n %:+ (mMn %:+ nMm))
                     === (n %:+ mMn) %:+ nMm
                         `because` sym (plusAssoc n mMn nMm)
                     =~= m %:+ nMm
                     =~= n
                     === n %:+ sZero
                         `because` sym (plusZeroR n)
            nMmEQ0 = plusEqZeroL mMn nMm pEQ0

        in sym $ start m
             =~= n %:+ mMn
             === n %:+ sZero  `because` plusCongR n nMmEQ0
             === n            `because` plusZeroR n

  plusMonotone :: Sing (n :: nat) -> Sing m -> Sing l -> Sing k
               -> IsTrue (n :<= m) -> IsTrue (l :<= k)
               -> IsTrue (n :+ l :<= m :+ k)
  plusMonotone n m l k nLEm lLEk =
    case (leqWitness n m nLEm, leqWitness l k lLEk) of
      (DiffNat _ mMINn, DiffNat _ kMINl) ->
        let r = mMINn %:+ kMINl
        in leqStep (n %:+ l) (m %:+ k) r $
           start (n %:+ l %:+ r)
             === n %:+ (l %:+ r)
                 `because` plusAssoc n l r
             =~= n %:+ (l %:+ (mMINn %:+ kMINl))
             === n %:+ (l %:+ (kMINl %:+ mMINn))
                 `because` plusCongR n (plusCongR l (plusComm mMINn kMINl))
             === n %:+ ((l %:+ kMINl) %:+ mMINn)
                 `because` plusCongR n (sym $ plusAssoc l kMINl mMINn)
             =~= n %:+ (k %:+ mMINn)
             === n %:+ (mMINn %:+ k)
                 `because` plusCongR n (plusComm k mMINn)
             === n %:+ mMINn %:+ k
                 `because` sym (plusAssoc n mMINn k)
             =~= m %:+ k

  leqZeroElim :: Sing n -> IsTrue (n :<= Zero nat) -> n :~: Zero nat
  leqZeroElim n nLE0 =
    case viewLeq n sZero nLE0 of
      LeqZero _ -> Refl
      LeqSucc _ pZ _ -> absurd $ succNonCyclic pZ Refl

  plusCancelLeqR :: Sing (n :: nat) -> Sing m -> Sing l
                 -> IsTrue (n :+ l :<= m :+ l)
                 -> IsTrue (n :<= m)
  plusCancelLeqR n m l nlLEQml =
    case leqWitness (n %:+ l) (m %:+ l) nlLEQml of
      DiffNat _ k ->
        let pf = plusEqCancelR (n %:+ k) m l $
                 start ((n %:+ k) %:+ l)
                   === n %:+ (k %:+ l) `because` plusAssoc n k l
                   === n %:+ (l %:+ k) `because` plusCongR n (plusComm k l)
                   === n %:+ l %:+ k   `because` sym (plusAssoc n l k)
                   =~= m %:+ l
        in leqStep n m k pf

  plusCancelLeqL :: Sing (n :: nat) -> Sing m -> Sing l
                 -> IsTrue (n :+ m :<= n :+ l)
                 -> IsTrue (m :<= l)
  plusCancelLeqL n m l nmLEQnl =
    plusCancelLeqR m l n $
    coerceLeqL (plusComm n m) (l %:+ n) $
    coerceLeqR (n %:+ m) (plusComm n l) nmLEQnl

  succLeqZeroAbsurd :: Sing n -> IsTrue (S n :<= Zero nat) -> Void
  succLeqZeroAbsurd n leq =
    succNonCyclic n (leqZeroElim (sSucc n) leq)

  minLeqL :: Sing (n :: nat) -> Sing m -> IsTrue (Min n m :<= n)
  minLeqR :: Sing (n :: nat) -> Sing m -> IsTrue (Min n m :<= m)
  minLargest :: Sing (l :: nat) ->  Sing n -> Sing m
             -> IsTrue (l :<= n) -> IsTrue (l :<= m)
             -> IsTrue (l :<= Min n m)

  maxLeqL  :: Sing (n :: nat) -> Sing m -> IsTrue (n :<= Max n m)
  maxLeqR  :: Sing (n :: nat) -> Sing m -> IsTrue (m :<= Max n m)
  maxLeast :: Sing (l :: nat) ->  Sing n -> Sing m
           -> IsTrue (n :<= l) -> IsTrue (m :<= l)
           -> IsTrue (Max n m :<= l)

