{-# LANGUAGE DataKinds, EmptyCase, ExplicitForAll, FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances, GADTs, KindSignatures                       #-}
{-# LANGUAGE MultiParamTypeClasses, PatternSynonyms, PolyKinds, RankNTypes  #-}
{-# LANGUAGE ScopedTypeVariables, TemplateHaskell, TypeFamilies, TypeInType #-}
module Data.Type.Natural.Class.Order
       (PeanoOrder(..), DiffNat(..), LeqView(..),
        FlipOrdering, sFlipOrdering, coerceLeqL, coerceLeqR,
        sLeqCongL, sLeqCongR, sLeqCong
       ) where
import Data.Type.Natural.Class.Arithmetic

import Data.Singletons.Decide
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TH
import Data.Type.Equality
import Data.Void
import Proof.Equational
import Proof.Propositional

data LeqView (n :: nat) (m :: nat) where
  LeqZero :: Sing n -> LeqView (Zero nat) n
  LeqSucc :: Sing n -> Sing m -> IsTrue (n :<= m) -> LeqView (Succ n) (Succ m)

data DiffNat n m where
  DiffNat :: Sing n -> Sing m -> DiffNat n (n :+ m)

newtype LeqWitPf n = LeqWitPf { leqWitPf :: forall m. Sing m -> IsTrue (n :<= m) -> DiffNat n m }
newtype LeqStepPf n = LeqStepPf { leqStepPf :: forall m l. Sing m -> Sing l -> n :+ l :~: m -> IsTrue (n :<= m) }

succDiffNat :: IsPeano nat
            => Sing n -> Sing m -> DiffNat (n :: nat) m -> DiffNat (Succ n) (Succ m)
succDiffNat _ _ (DiffNat n m) = coerce (plusSuccL n m) $ DiffNat (sSucc n) m

coerceLeqL :: forall (n :: nat) m l . IsPeano nat => n :~: m -> Sing l
           -> IsTrue (n :<= l) -> IsTrue (m :<= l)
coerceLeqL Refl _ Witness = Witness

coerceLeqR :: forall (n :: nat) m l . IsPeano nat =>  Sing l -> n :~: m
           -> IsTrue (l :<= n) -> IsTrue (l :<= m)
coerceLeqR _ Refl Witness = Witness

singletonsOnly [d|
  flipOrdering :: Ordering -> Ordering
  flipOrdering EQ = EQ
  flipOrdering LT = GT
  flipOrdering GT = LT
 |]

congFlipOrdering :: a :~: b -> FlipOrdering a :~: FlipOrdering b
congFlipOrdering Refl = Refl

compareCongR :: Sing (a :: k) -> b :~: c -> Compare a b :~: Compare a c
compareCongR _ Refl = Refl

sLeqCong :: a :~: b -> c :~: d -> (a :<= c) :~: (b :<= d)
sLeqCong Refl Refl = Refl

sLeqCongL :: a :~: b -> Sing c -> (a :<= c) :~: (b :<= c)
sLeqCongL Refl _ = Refl

sLeqCongR :: Sing a -> b :~: c -> (a :<= b) :~: (a :<= c)
sLeqCongR _ Refl = Refl

newtype LTSucc n = LTSucc { proofLTSucc :: Compare n (Succ n) :~: 'LT }
newtype CmpSuccStepR (n :: nat) =
  CmpSuccStepR { proofCmpSuccStepR :: forall (m :: nat). Sing m
                                   -> Compare n m :~: 'LT
                                   -> Compare n (Succ m) :~: 'LT
                                   }

newtype LeqViewRefl n = LeqViewRefl { proofLeqViewRefl :: LeqView n n }

class (SOrd nat, IsPeano nat) => PeanoOrder nat where
  {-# MINIMAL ( succLeqToLT, cmpZero, leqRefl
              | leqZero, leqSucc , viewLeq
              | leqWitness, leqStep
              ),
              eqlCmpEQ, ltToLeq, eqToRefl,
              flipCompare, leqToCmp,
              leqReversed, lneqSuccLeq, lneqReversed,
              (leqToMin, geqToMin | minLeqL, minLeqR, minLargest),
              (leqToMax, geqToMax | maxLeqL, maxLeqR, maxLeast) #-}

  leqToCmp :: Sing (a :: nat) -> Sing b -> IsTrue (a :<= b)
           -> Either (a :~: b) (Compare a b :~: 'LT)
  eqlCmpEQ :: Sing (a :: nat) -> Sing b -> a :~: b -> Compare a b :~: 'EQ
  eqToRefl :: Sing (a :: nat) -> Sing b -> Compare a b :~: 'EQ -> a :~: b

  flipCompare :: Sing (a :: nat) -> Sing b
              -> FlipOrdering (Compare a b) :~: Compare b a

  ltToNeq :: Sing (a :: nat) -> Sing b -> Compare a b :~: 'LT
           -> a :~: b -> Void
  ltToNeq a b aLTb aEQb = eliminate $
    start SLT
      === sCompare a b `because` sym aLTb
      === SEQ          `because` eqlCmpEQ a b aEQb

  leqNeqToLT :: Sing (a :: nat) -> Sing b -> IsTrue (a :<= b) -> (a :~: b -> Void) -> Compare a b :~: 'LT
  leqNeqToLT a b aLEQb aNEQb = either (absurd . aNEQb) id $ leqToCmp a b aLEQb


  succLeqToLT :: Sing (a :: nat) -> Sing b -> IsTrue (S a :<= b) -> Compare a b :~: 'LT
  succLeqToLT a b saLEQb =
    case leqWitness (sSucc a) b saLEQb of
      DiffNat _ k -> let aLEQb = leqStep a b (sSucc k) $
                                 start (a %:+ sSucc k)
                                   === sSucc (a %:+ k) `because` plusSuccR a k
                                   === sSucc a %:+ k   `because` sym (plusSuccL a k)
                                   =~= b
                         aNEQb aeqb = succNonCyclic k $ plusEqCancelL a (sSucc k) sZero $
                                     start (a %:+ sSucc k)
                                      === sSucc (a %:+ k) `because` plusSuccR a k
                                      === (sSucc a) %:+ k `because` sym (plusSuccL a k)
                                      =~= b
                                      === a               `because` sym aeqb
                                      === a %:+ sZero     `because` sym (plusZeroR a)
                     in leqNeqToLT a b aLEQb aNEQb

  ltToLeq :: Sing (a :: nat) -> Sing b -> Compare a b :~: 'LT
          -> IsTrue (a :<= b)

  gtToLeq :: Sing (a :: nat) -> Sing b -> Compare a b :~: 'GT
          -> IsTrue (b :<= a)
  gtToLeq n m nGTm = ltToLeq m n $
    start (sCompare m n) === sFlipOrdering (sCompare n m) `because` sym (flipCompare n m)
                         === sFlipOrdering SGT            `because` congFlipOrdering nGTm
                         =~= SLT

  ltToSuccLeq :: Sing (a :: nat) -> Sing b -> Compare a b :~: 'LT
              -> IsTrue (Succ a :<= b)
  ltToSuccLeq n m nLTm =
     leqNeqToSuccLeq n m (ltToLeq n m nLTm) (ltToNeq n m nLTm)

  cmpZero :: Sing a -> Compare (Zero nat) (Succ a) :~: 'LT
  cmpZero sn = leqToLT sZero (sSucc sn) $ leqStep (sSucc sZero) (sSucc sn) sn $
               start (sSucc sZero %:+ sn)
                 === sSucc (sZero %:+ sn) `because` plusSuccL sZero sn
                 === sSucc sn             `because` succCong (plusZeroL sn)

  leqToGT :: Sing (a :: nat) -> Sing b -> IsTrue (Succ b :<= a)
              -> Compare a b :~: 'GT
  leqToGT a b sbLEQa =
    start (sCompare a b)
      === sFlipOrdering (sCompare b a) `because` sym (flipCompare b a)
      === sFlipOrdering SLT            `because` congFlipOrdering (leqToLT b a sbLEQa)
      =~= SGT

  cmpZero' :: Sing a -> Either (Compare (Zero nat) a :~: 'EQ) (Compare (Zero nat) a :~: 'LT)
  cmpZero' n =
    case zeroOrSucc n of
      IsZero    -> Left $ eqlCmpEQ sZero n Refl
      IsSucc n' -> Right $ cmpZero n'

  zeroNoLT :: Sing a -> Compare a (Zero nat) :~: 'LT -> Void
  zeroNoLT n eql =
    case cmpZero' n of
      Left cmp0nEQ -> eliminate $
        start SGT
          =~= sFlipOrdering SLT
          === sFlipOrdering (sCompare n sZero) `because` congFlipOrdering (sym eql)
          === sCompare sZero n                 `because` flipCompare n sZero
          === SEQ                              `because` cmp0nEQ
      Right cmp0nLT -> eliminate $
        start SGT
          =~= sFlipOrdering SLT
          === sFlipOrdering (sCompare n sZero) `because` congFlipOrdering (sym eql)
          === sCompare sZero n                 `because` flipCompare n sZero
          === SLT                              `because` cmp0nLT

  ltRightPredSucc :: Sing (a :: nat) -> Sing b -> Compare a b :~: 'LT -> b :~: Succ (Pred b)
  ltRightPredSucc a b aLTb =
    case zeroOrSucc b of
      IsZero -> absurd $ zeroNoLT a aLTb
      IsSucc b' -> sym $
        start (sSucc (sPred b))
          =~= sSucc (sPred (sSucc b'))
          === sSucc b' `because` succCong (predSucc b')
          =~= b

  cmpSucc :: Sing (n :: nat) -> Sing m -> Compare n m :~: Compare (Succ n) (Succ m)
  cmpSucc n m =
    case sCompare n m of
      SEQ -> let nEQm = eqToRefl n m Refl
             in sym $ eqlCmpEQ (sSucc n) (sSucc m) $ succCong nEQm
      SLT -> case leqWitness (sSucc n) m $ ltToSuccLeq n m Refl of
               DiffNat _ k ->
                 sym $ succLeqToLT (sSucc n) (sSucc m) $
                 leqStep (sSucc (sSucc n)) (sSucc m) k $
                 start (sSucc (sSucc n) %:+ k)
                   === sSucc (sSucc n %:+ k)    `because` plusSuccL (sSucc n) k
                   =~= sSucc m
      SGT -> case leqWitness (sSucc m) n $ ltToSuccLeq m n (sym $ flipCompare n m) of
               DiffNat _ k ->
                 let pf = (succLeqToLT (sSucc m) (sSucc n) $
                          leqStep (sSucc (sSucc m)) (sSucc n) k $
                          start (sSucc (sSucc m) %:+ k)
                            === sSucc (sSucc m %:+ k)    `because` plusSuccL (sSucc m) k
                            =~= sSucc n)
                 in start (sCompare n m)
                      =~= SGT
                      =~= sFlipOrdering SLT
                      === sFlipOrdering (sCompare (sSucc m) (sSucc n)) `because` congFlipOrdering (sym pf)
                      === sCompare (sSucc n) (sSucc m) `because` flipCompare (sSucc m) (sSucc n)

  ltSucc :: Sing (a :: nat) -> Compare a (Succ a) :~: 'LT
  ltSucc = proofLTSucc . induction base step
    where
      base :: LTSucc (Zero nat)
      base = LTSucc $ cmpZero (sZero :: Sing (Zero nat))

      step :: Sing (n :: nat) -> LTSucc n -> LTSucc (Succ n)
      step n (LTSucc ih) = LTSucc $
        start (sCompare (sSucc n) (sSucc (sSucc n)))
          === sCompare n (sSucc n) `because` sym (cmpSucc n (sSucc n))
          === SLT `because` ih

  cmpSuccStepR :: Sing (n :: nat) -> Sing m -> Compare n m :~: 'LT
               -> Compare n (Succ m) :~: 'LT
  cmpSuccStepR = proofCmpSuccStepR . induction base step
    where
      base :: CmpSuccStepR (Zero nat)
      base = CmpSuccStepR $ \m _ -> cmpZero m

      step :: Sing (n :: nat) -> CmpSuccStepR n -> CmpSuccStepR (Succ n)
      step n (CmpSuccStepR ih) = CmpSuccStepR $ \m snltm ->
        case zeroOrSucc m of
          IsZero -> absurd $ zeroNoLT (sSucc n) snltm
          IsSucc m' ->
            let nLTm' = trans (cmpSucc n m') snltm
            in start (sCompare (sSucc n) (sSucc m))
                 =~= sCompare (sSucc n) (sSucc (sSucc m'))
                 === sCompare n (sSucc m') `because` sym (cmpSucc n (sSucc m'))
                 === SLT                   `because` ih m' nLTm'

  ltSuccLToLT :: Sing (n :: nat) -> Sing m -> Compare (Succ n) m :~: 'LT
           -> Compare n m :~: 'LT
  ltSuccLToLT n m snLTm =
    case zeroOrSucc m of
      IsZero -> absurd $ zeroNoLT (sSucc n) snLTm
      IsSucc m' ->
        let nLTm = cmpSucc n m' `trans` snLTm
        in start (sCompare n (sSucc m'))
             === SLT `because` cmpSuccStepR n m' nLTm

  leqToLT :: Sing (a :: nat) -> Sing b -> IsTrue (Succ a :<= b)
           -> Compare a b :~: 'LT
  leqToLT n m snLEQm =
    case leqToCmp (sSucc n) m snLEQm of
      Left Refl ->
        start (sCompare n m)
          =~= sCompare n (sSucc n)
          === SLT `because` ltSucc n
      Right nLTm -> ltSuccLToLT n m nLTm

  leqZero :: Sing n -> IsTrue (Zero nat :<= n)
  leqZero sn =
    case zeroOrSucc sn of
      IsZero   -> leqRefl sn
      IsSucc pn -> ltToLeq sZero sn $ cmpZero pn

  leqSucc :: Sing (n :: nat) -> Sing m -> IsTrue (n :<= m) -> IsTrue (Succ n :<= Succ m)
  leqSucc n m nLEQm =
    case leqToCmp n m nLEQm of
      Left  Refl  -> leqRefl (sSucc n)
      Right nLTm -> ltToLeq (sSucc n) (sSucc m) $ sym (cmpSucc n m) `trans` nLTm

  fromLeqView :: LeqView (n :: nat) m -> IsTrue (n :<= m)
  fromLeqView (LeqZero n) = leqZero n
  fromLeqView (LeqSucc n m nLEQm) = leqSucc n m nLEQm

  leqViewRefl :: Sing (n :: nat) -> LeqView n n
  leqViewRefl = proofLeqViewRefl . induction base step
    where
      base :: LeqViewRefl (Zero nat)
      base = LeqViewRefl $ LeqZero sZero
      step :: Sing (n :: nat) -> LeqViewRefl n -> LeqViewRefl (Succ n)
      step n (LeqViewRefl nLEQn) =
        LeqViewRefl $ LeqSucc n n (fromLeqView nLEQn)

  viewLeq :: forall n m . Sing (n :: nat) -> Sing m -> IsTrue (n :<= m) -> LeqView n m
  viewLeq n m nLEQm =
    case (zeroOrSucc n, leqToCmp n m nLEQm) of
      (IsZero, _)    -> LeqZero m
      (_, Left Refl) -> leqViewRefl n
      (IsSucc n', Right nLTm) ->
         let sm'EQm = ltRightPredSucc n m nLTm
             m' = sPred m
             n'LTm' = cmpSucc n' m' `trans` compareCongR n (sym sm'EQm) `trans` nLTm
         in coerce (sym sm'EQm) $ LeqSucc n' m' $ ltToLeq n' m' n'LTm'

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

  leqNeqToSuccLeq :: Sing (n :: nat) -> Sing m -> IsTrue (n :<= m) -> (n :~: m -> Void) -> IsTrue (Succ n :<= m)
  leqNeqToSuccLeq n m nLEQm nNEQm =
    case leqWitness n m nLEQm of
      DiffNat _ k ->
        case zeroOrSucc k of
          IsZero -> absurd $ nNEQm $ sym $ plusZeroR n
          IsSucc k' -> leqStep (sSucc n) m k' $
            start (sSucc n %:+ k')
              === sSucc (n %:+ k') `because` plusSuccL n k'
              === n %:+ sSucc k'   `because` sym (plusSuccR n k')
              =~= m

  leqRefl :: Sing (n :: nat) -> IsTrue (n :<= n)
  leqRefl sn = leqStep sn sn sZero (plusZeroR sn)

  leqSuccStepR :: Sing (n :: nat) -> Sing m -> IsTrue (n :<= m) -> IsTrue (n :<= Succ m)
  leqSuccStepR n m nLEQm =
    case leqWitness n m nLEQm of
      DiffNat _ k -> leqStep n (sSucc m) (sSucc k) $
        start (n %:+ sSucc k) === sSucc (n %:+ k) `because` plusSuccR n k =~= sSucc m

  leqSuccStepL :: Sing (n :: nat) -> Sing m -> IsTrue (Succ n :<= m) -> IsTrue (n :<= m)
  leqSuccStepL n m snLEQm =
     leqTrans n (sSucc n) m (leqSuccStepR n n $ leqRefl n) snLEQm

  leqReflexive :: Sing (n :: nat) -> Sing m -> n :~: m -> IsTrue (n :<= m)
  leqReflexive n _ Refl = leqRefl n

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

  plusMonotoneL :: Sing (n :: nat) -> Sing m -> Sing (l :: nat) -> IsTrue (n :<= m)
           -> IsTrue (n :+ l :<= m :+ l)
  plusMonotoneL n m l leq = plusMonotone n m l l leq (leqRefl l)

  plusMonotoneR :: Sing n -> Sing m -> Sing (l :: nat) -> IsTrue (m :<= l)
           -> IsTrue (n :+ m :<= n :+ l)
  plusMonotoneR n m l leq = plusMonotone n n m l (leqRefl n) leq

  plusLeqL :: Sing (n :: nat) -> Sing m -> IsTrue (n :<= n :+ m)
  plusLeqL n m = leqStep n (n %:+ m) m Refl

  plusLeqR :: Sing (n :: nat) -> Sing m -> IsTrue (m :<= n :+ m)
  plusLeqR n m = leqStep m (n %:+ m) n $ plusComm m n

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

  succLeqZeroAbsurd' :: Sing n -> (S n :<= Zero nat) :~: 'False
  succLeqZeroAbsurd' n =
    case sSucc n %:<= sZero of
      STrue  -> absurd $ succLeqZeroAbsurd n Witness
      SFalse -> Refl

  succLeqAbsurd :: Sing (n :: nat) -> IsTrue (S n :<= n) -> Void
  succLeqAbsurd n snLEQn =
    eliminate $
      start SLT
        === sCompare n n `because` sym (succLeqToLT n n snLEQn)
        === SEQ          `because` eqlCmpEQ n n Refl

  succLeqAbsurd' :: Sing (n :: nat) -> (S n :<= n) :~: 'False
  succLeqAbsurd' n =
    case sSucc n %:<= n of
      STrue -> absurd $ succLeqAbsurd n Witness
      SFalse -> Refl

  notLeqToLeq :: ((n :<= m) ~ 'False) => Sing (n :: nat) -> Sing m -> IsTrue (m :<= n)
  notLeqToLeq n m =
    case sCompare n m of
      SLT -> eliminate $ ltToLeq n m Refl
      SEQ -> eliminate $ leqReflexive n m $ eqToRefl n m Refl
      SGT -> gtToLeq n m Refl

  leqSucc' :: Sing (n :: nat) -> Sing m -> (n :<= m) :~: (Succ n :<= Succ m)
  leqSucc' n m =
    case n %:<= m of
      STrue ->
        case leqSucc n m Witness of
          Witness -> Refl
      SFalse ->
        case sSucc n %:<= sSucc m of
          SFalse -> Refl
          STrue  ->
            case viewLeq (sSucc n) (sSucc m) Witness of
              LeqZero _ -> absurd $ succNonCyclic n Refl
              LeqSucc n' m' Witness ->
                eliminate $
                start STrue
                  =~= (n' %:<= m')
                  === (n  %:<= m)   `because` sLeqCong (succInj' n' n Refl) (succInj' m' m Refl)
                  =~= SFalse

  leqToMin :: Sing (n :: nat) -> Sing m -> IsTrue (n :<= m) -> Min n m :~: n
  leqToMin n m nLEQm =
     leqAntisymm (sMin n m) n (minLeqL n m)
                 (minLargest n n m (leqRefl n) nLEQm)

  geqToMin :: Sing (n :: nat) -> Sing m -> IsTrue (m :<= n) -> Min n m :~: m
  geqToMin n m mLEQn =
     leqAntisymm (sMin n m) m (minLeqR n m)
                 (minLargest m n m mLEQn (leqRefl m))

  minComm :: Sing (n :: nat) -> Sing m -> Min n m :~: Min m n
  minComm n m =
    case n %:<= m of
      STrue -> start (sMin n m) === n        `because` leqToMin n m Witness
                                === sMin m n `because` sym (geqToMin m n Witness)
      SFalse -> start (sMin n m) === m        `because` geqToMin n m (notLeqToLeq n m)
                                 === sMin m n `because` sym (leqToMin m n $ notLeqToLeq n m)

  minLeqL :: Sing (n :: nat) -> Sing m -> IsTrue (Min n m :<= n)
  minLeqL n m =
    case n %:<= m of
      STrue  -> leqReflexive (sMin n m) n $ leqToMin n m Witness
      SFalse -> let mLEQn = notLeqToLeq n m
                in leqTrans (sMin n m) m n
                     (leqReflexive (sMin n m) m (geqToMin n m mLEQn)) $
                     mLEQn

  minLeqR :: Sing (n :: nat) -> Sing m -> IsTrue (Min n m :<= m)
  minLeqR n m = leqTrans (sMin n m) (sMin m n) m
                  (leqReflexive (sMin n m) (sMin m n) $ minComm n m)
                  (minLeqL m n)

  minLargest :: Sing (l :: nat) ->  Sing n -> Sing m
             -> IsTrue (l :<= n) -> IsTrue (l :<= m)
             -> IsTrue (l :<= Min n m)
  minLargest l n m lLEQn lLEQm =
    withSingI l $ withSingI n $ withSingI m $ withSingI (sMin n m) $
    case n %:<= m of
      STrue -> leqTrans l n (sMin n m) lLEQn $
               leqReflexive sing sing  $ sym $ leqToMin n m Witness
      SFalse ->
        let mLEQn = notLeqToLeq n m
        in leqTrans l m (sMin n m) lLEQm $
           leqReflexive sing sing  $ sym $ geqToMin n m mLEQn

  leqToMax :: Sing (n :: nat) -> Sing m -> IsTrue (n :<= m) -> Max n m :~: m
  leqToMax n m nLEQm =
     leqAntisymm (sMax n m) m (maxLeast m n m nLEQm (leqRefl m)) (maxLeqR n m)

  geqToMax :: Sing (n :: nat) -> Sing m -> IsTrue (m :<= n) -> Max n m :~: n
  geqToMax n m mLEQn =
     leqAntisymm (sMax n m) n (maxLeast n n m (leqRefl n) mLEQn) (maxLeqL n m)

  maxComm :: Sing (n :: nat) -> Sing m -> Max n m :~: Max m n
  maxComm n m =
    case n %:<= m of
      STrue -> start (sMax n m) === m        `because` leqToMax n m Witness
                                === sMax m n `because` sym (geqToMax m n Witness)
      SFalse -> start (sMax n m) === n        `because` geqToMax n m (notLeqToLeq n m)
                                 === sMax m n `because` sym (leqToMax m n $ notLeqToLeq n m)

  maxLeqR :: Sing (n :: nat) -> Sing m -> IsTrue (m :<= Max n m)
  maxLeqR n m =
    case n %:<= m of
      STrue  -> leqReflexive m (sMax n m) $ sym $ leqToMax n m Witness
      SFalse -> let mLEQn = notLeqToLeq n m
                in leqTrans m n (sMax n m) mLEQn
                     (leqReflexive n (sMax n m) (sym $ geqToMax n m mLEQn))

  maxLeqL :: Sing (n :: nat) -> Sing m -> IsTrue (n :<= Max n m)
  maxLeqL n m = leqTrans n (sMax m n) (sMax n m)
                  (maxLeqR m n)
                  (leqReflexive (sMax m n) (sMax n m) $ maxComm m n)

  maxLeast :: Sing (l :: nat) ->  Sing n -> Sing m
             -> IsTrue (n :<= l) -> IsTrue (m :<= l)
             -> IsTrue (Max n m :<= l)
  maxLeast l n m lLEQn lLEQm =
    withSingI l $ withSingI n $ withSingI m $ withSingI (sMax n m) $
    case n %:<= m of
      STrue -> leqTrans (sMax n m) m l
               (leqReflexive sing sing  $ leqToMax n m Witness)
               lLEQm
      SFalse ->
        let mLEQn = notLeqToLeq n m
        in leqTrans (sMax n m) n l
           (leqReflexive sing sing  $ geqToMax n m mLEQn)
           lLEQn

  leqReversed  :: Sing (n :: nat) -> Sing m -> (n :<= m) :~: (m :>= n)
  lneqSuccLeq  :: Sing (n :: nat) -> Sing m -> (n :< m)  :~: (Succ n :<= m)
  lneqReversed :: Sing (n :: nat) -> Sing m -> (n :< m)  :~: (m :> n)

  lneqToLT :: Sing (n :: nat) -> Sing (m :: nat) -> IsTrue (n :< m)
           -> Compare n m :~: 'LT
  lneqToLT n m nLNEm =
    succLeqToLT n m $ coerce (lneqSuccLeq n m) nLNEm

  ltToLneq :: Sing (n :: nat) -> Sing (m :: nat) -> Compare n m :~: 'LT
           -> IsTrue (n :< m)
  ltToLneq n m nLTm =
    coerce (sym $ lneqSuccLeq n m) $ ltToSuccLeq n m nLTm

  lneqZero :: Sing (a :: nat) -> IsTrue (Zero nat :< Succ a)
  lneqZero n = ltToLneq sZero (sSucc n) $ cmpZero n

  lneqSucc :: Sing (n :: nat) -> IsTrue (n :< Succ n)
  lneqSucc n = ltToLneq n (sSucc n) $ ltSucc n

  succLneqSucc :: Sing (n :: nat) -> Sing (m :: nat)
               -> (n :< m) :~: (Succ n :< Succ m)
  succLneqSucc n m =
    start (n %:< m)
      === (sSucc n %:<= m)               `because` lneqSuccLeq n m
      === (sSucc (sSucc n) %:<= sSucc m) `because` leqSucc' (sSucc n) m
      === (sSucc n %:< sSucc m)          `because` sym (lneqSuccLeq (sSucc n) (sSucc m))

  lneqRightPredSucc :: Sing (n :: nat) -> Sing (m :: nat) -> IsTrue (n :< m)
                    -> m :~: Succ (Pred m)
  lneqRightPredSucc n m nLNEQm = ltRightPredSucc n m $ lneqToLT n m nLNEQm

  plusStrictMonotone :: Sing (n :: nat) -> Sing m -> Sing l -> Sing k
                     -> IsTrue (n :< m) -> IsTrue (l :< k)
                     -> IsTrue (n :+ l :< m :+ k)
  plusStrictMonotone n m l k nLNm lLNk =
    coerce (sym $ lneqSuccLeq (n %:+ l) (m %:+ k)) $
      flip coerceLeqL (m %:+ k) (plusSuccL n l) $
      plusMonotone (sSucc n) m l k
        (coerce (lneqSuccLeq n m) nLNm)
        (leqTrans l (sSucc l) k (leqSuccStepR l l (leqRefl l)) $
           coerce (lneqSuccLeq l k) lLNk)

  maxZeroL :: Sing n -> Max (Zero nat) n :~: n
  maxZeroL n = leqToMax sZero n (leqZero n)

  maxZeroR  :: Sing n -> Max n (Zero nat) :~: n
  maxZeroR n = geqToMax n sZero (leqZero n)

  minZeroL :: Sing n -> Min (Zero nat) n :~: Zero nat
  minZeroL n = leqToMin sZero n (leqZero n)

  minZeroR  :: Sing n -> Min n (Zero nat) :~: Zero nat
  minZeroR n = geqToMin n sZero (leqZero n)

  minusSucc :: Sing (n :: nat) -> Sing m -> IsTrue (m :<= n) -> Succ n :- m :~: Succ (n :- m)
  minusSucc n m mLEQn =
    case leqWitness m n mLEQn of
      DiffNat _ k ->
        start (sSucc n %:- m)
          =~= sSucc (m %:+ k) %:- m
          === (m %:+ sSucc k) %:- m  `because` minusCongL (sym $ plusSuccR m k) m
          === (sSucc k %:+ m) %:- m  `because` minusCongL (plusComm m (sSucc k)) m
          === sSucc k                `because` plusMinus (sSucc k) m
          === sSucc (k %:+ m %:- m)  `because` succCong (sym $ plusMinus k m)
          === sSucc (m %:+ k %:- m)  `because` succCong (minusCongL (plusComm k m) m)
          =~= sSucc (n %:- m)

