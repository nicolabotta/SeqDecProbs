> module Main

> import Decidable.Order

> import Data.Fin
> import Data.Vect
> import Data.List
> import Data.List.Quantifiers
> import Data.So
> import Control.Isomorphism
> import Effects
> import Effect.Exception
> import Effect.StdIO
> import Syntax.PreorderReasoning

> import SeqDecProbsCoreAssumptions
> import SeqDecProbsCoreTheory
> import SeqDecProbsHelpers
> import SeqDecProbsUtils

> import ListOperations
> import ListProperties
> import BoundedNat
> import BoundedNatOperations
> import BoundedNatProperties
> import LeftAheadRight
> import Sigma
> import SigmaOperations
> import SigmaProperties
> import NatProperties
> import Finite
> import FiniteOperations
> import FiniteProperties
> import Unique
> import Decidable
> import UnitProperties
> import VoidProperties
> import Opt
> import TotalPreorder
> import EffectException
> import EffectStdIO
> import FinOperations
> import PairsOperations

> %default total
> %auto_implicits off


> -- %logging 5

Like "SeqDecProbsExample2.lidr", but now |step t x y| is empty in states
corresponding to |maxColumn|, no matter which |y| is selected! Thus,
such states are not viable for more than zero steps. Attemps at making
more than zero decision steps starting from |maxColumn| should be
detected and rejected.



* The monad M (List):


** M is a monad:

> SeqDecProbsCoreAssumptions.M = List
> SeqDecProbsCoreAssumptions.fmap = ListOperations.fmap
> SeqDecProbsCoreAssumptions.ret = ListOperations.ret
> SeqDecProbsCoreAssumptions.bind = ListOperations.bind


** M is a container monad:

> SeqDecProbsCoreAssumptions.Elem = Data.List.Elem
> SeqDecProbsCoreAssumptions.NonEmpty = ListOperations.NonEmpty
> SeqDecProbsCoreAssumptions.All = Data.List.Quantifiers.All
> SeqDecProbsCoreAssumptions.elemNonEmptySpec0 = ListProperties.elemNonEmptySpec0
> SeqDecProbsCoreAssumptions.elemNonEmptySpec1 = ListProperties.elemNonEmptySpec1
> SeqDecProbsCoreAssumptions.tagElem = ListOperations.tagElem
> SeqDecProbsCoreAssumptions.containerMonadSpec3 = ListProperties.containerMonadSpec3



* The decision process:

> maxColumn : Nat
> maxColumn = 10

> nColumns : Nat
> nColumns = S maxColumn


** States:

> SeqDecProbsCoreAssumptions.State t = LTB nColumns


** Controls:

> SeqDecProbsCoreAssumptions.Ctrl t x = LeftAheadRight


** Transition function:

> SeqDecProbsCoreAssumptions.step t (MkSigma Z prf) Left =
>   [MkSigma maxColumn (ltIdS maxColumn)]
> SeqDecProbsCoreAssumptions.step t (MkSigma (S n) prf) Left with (decLT (S n) maxColumn)
>   | (Yes p)     = [MkSigma n (ltLemma1 n nColumns prf)]
>   | (No contra) = []
> SeqDecProbsCoreAssumptions.step t (MkSigma n prf) Ahead with (decLT n maxColumn)
>   | (Yes p)     = [MkSigma n prf]
>   | (No contra) = []
> SeqDecProbsCoreAssumptions.step t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = [MkSigma (S n) (LTESucc p)]
>   | (No contra) = []

> stepLemma0 : {t : Nat} -> 
>              (x : State t) -> (outl x `LT` maxColumn) -> step t x Ahead = [x]
> stepLemma0 {t} (MkSigma i prf) p with (decLT i maxColumn)
>   | (Yes _) = Refl
>   | (No contra) = void (contra p)

> stepLemma1 : {t : Nat} -> 
>              (x : State t) -> (outl x `LT` maxColumn) -> 
>              SeqDecProbsCoreAssumptions.NonEmpty (step t x Ahead)
> stepLemma1 {t} x prf with (decLT (outl x) maxColumn)
>   | (Yes p) = s3 where
>     s1 : SeqDecProbsCoreAssumptions.NonEmpty [x] 
>     s1 = SeqDecProbsCoreAssumptions.elemNonEmptySpec0 x [x] Here
>     s2 : [x] = step t x Ahead
>     s2 = sym (stepLemma0 x p)
>     s3 : SeqDecProbsCoreAssumptions.NonEmpty (step t x Ahead)
>     s3 = replace s2 s1
>   | (No contra) = void (contra prf)



** Reward function:

> SeqDecProbsCoreAssumptions.Val = Nat

> SeqDecProbsCoreAssumptions.reward t x y (MkSigma c _) =
>   if c == Z
>   then (S Z)
>   else if (S c) == nColumns
>        then (S (S Z))
>        else Z

> SeqDecProbsCoreAssumptions.plus = Prelude.Nat.plus
> SeqDecProbsCoreAssumptions.zero = Z

> SeqDecProbsCoreAssumptions.LTE = Prelude.Nat.LTE
> SeqDecProbsCoreAssumptions.reflexiveLTE {a} = NatProperties.reflexiveLTE a
> SeqDecProbsCoreAssumptions.transitiveLTE {a} {b} {c} = NatProperties.transitiveLTE a b c
> SeqDecProbsCoreAssumptions.totalLTE {a} {b} = NatProperties.totalLTE a b

> SeqDecProbsCoreAssumptions.monotonePlusLTE = NatProperties.monotoneNatPlusLTE

** M is measurable:

> SeqDecProbsCoreAssumptions.meas = sum
> SeqDecProbsCoreAssumptions.measMon = sumMon



* Viable and Reachable

> -- Viable : (n : Nat) -> State t -> Type
> SeqDecProbsCoreAssumptions.Viable  Z    _ = Unit
> SeqDecProbsCoreAssumptions.Viable (S n) x with (decLT (outl x) maxColumn)
>   | (Yes _) = Unit
>   | (No  _) = Void

> viableLemma0 : {t : Nat} -> {x : State t} -> Viable Z x = Unit
> viableLemma0 = Refl

> viableLemma1 : {t : Nat} -> {n : Nat} -> {x : State t} -> 
>                (outl x) `Prelude.Nat.LT` maxColumn -> Viable (S n) x = Unit
> viableLemma1 {t} {n} {x} prf with (decLT (outl x) maxColumn)
>   | (Yes _) = Refl
>   | (No contra) = void (contra prf)

> viableLemma2 : {t : Nat} -> {n : Nat} -> {x : State t} -> 
>                Not ((outl x) `Prelude.Nat.LT` maxColumn) -> Viable (S n) x = Void
> viableLemma2 {t} {n} {x} prf with (decLT (outl x) maxColumn)
>   | (Yes p) = void (prf p)
>   | (No _) = Refl

> viableLemma : {t : Nat} -> {n : Nat} ->
>               (x : State t) -> 
>               SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x Ahead)
> viableLemma {t} {n = Z} (MkSigma i prf) with (decLT i maxColumn)
>   | (Yes p) = res where
>     res : SeqDecProbsCoreAssumptions.All (Viable {t = S t} Z) [MkSigma i prf]
>     res = v :: Nil where
>       v : Viable {t = S t} Z (MkSigma i prf)
>       v with (decLT i maxColumn)
>         | (Yes _) = MkUnit
>         | (No  contra) = void (contra p)
>   | (No  _) = Nil
> viableLemma {t} {n = S m} (MkSigma i prf) with (decLT i maxColumn)
>   | (Yes p) = res where
>     res : SeqDecProbsCoreAssumptions.All (Viable {t = S t} (S m)) [MkSigma i prf]
>     res = v :: Nil where
>       v : Viable {t = S t} (S m) (MkSigma i prf)
>       v with (decLT i maxColumn)
>         | (Yes _) = MkUnit
>         | (No  contra) = void (contra p)
>   | (No  _) = Nil
> {-
> viableLemma {t} {n} (MkSigma i prf) with (decLT i maxColumn)
>   | (Yes p) = res where
>     res : SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) [MkSigma i prf]
>     res = v :: Nil where
>       v : Viable {t = S t} n (MkSigma i prf)
>       v with (decLT i maxColumn)
>         | (Yes _) = MkUnit
>         | (No  contra) = void (contra p)
>   | (No  _) = Nil
> -}

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x n
> SeqDecProbsCoreAssumptions.viableSpec1 {t} {n} x v with (decLT (outl x) maxColumn)
>   | (Yes prf) = MkSigma Ahead (ne, av) where
>     ne : SeqDecProbsCoreAssumptions.NonEmpty (step t x Ahead)
>     ne = stepLemma1 x prf
>     av : SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x Ahead)
>     av = viableLemma x 
>   | (No _) = void v

> -- Reachable : State t' -> Type
> SeqDecProbsCoreAssumptions.Reachable x' = Unit

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (step t x y)
> SeqDecProbsCoreAssumptions.reachableSpec1 {t} x r y = all (step t x y) where
>   all : (xs : List (State (S t))) -> SeqDecProbsCoreAssumptions.All (Reachable {t' = S t}) xs
>   all Nil = Nil
>   all (x :: xs) = MkUnit :: (all xs)



* Max and argmax

We want to implement |max|, |argmax|, |maxSpec| and |argmaxSpec|. This
can be easily done in terms of |Opt.max| and |Opt.argmax| if we can show
that |GoodCtrl t x n| is finite and, for every |t : Nat|, |x : State t|
such that |Viable (S n) x|, its cardinality is not zero. In turn,

< finiteGoodCtrl : {t : Nat} -> {n : Nat} -> 
<                  (x : State t) -> 
<                  Finite (GoodCtrl t x n) 

and

< cnzGoodCtrl : {t : Nat} -> {n : Nat} -> 
<               (x : State t) -> (v : Viable {t = t} (S n) x) ->
<               CardNotZ (finiteGoodCtrl {t} {n} x)

follow from finiteness of |All|

> -- finiteAll : {A : Type} -> {P : A -> Type} -> 
> --             Finite1 P -> (ma : M A) -> Finite (All P ma)
> SeqDecProbsHelpers.finiteAll = ListProperties.finiteAll

, finiteness of |Viable|

> -- finiteViable : {t : Nat} -> {n : Nat} -> 
> --                (x : State t) -> Finite (Viable {t} n x)
> SeqDecProbsHelpers.finiteViable {t} {n = Z}    _ = finiteUnit
> SeqDecProbsHelpers.finiteViable {t} {n = S m} x with (decLT (outl x) maxColumn)
>   | (Yes p) = s3 where
>     s1 : Finite Unit
>     s1 = finiteUnit
>     s2 : Viable {t} (S m) x = Unit
>     s2 = viableLemma1 {t = t} {n = m} {x = x} p
>     s3 : Finite (Viable {t} (S m) x)
>     s3 = replace (sym s2) s1
>   | (No  c) = s3 where 
>     s1 : Finite Void
>     s1 = finiteVoid
>     s2 : Viable {t} (S m) x = Void
>     s2 = viableLemma2 {t = t} {n = m} {x = x} c
>     s3 : Finite (Viable {t} (S m) x)
>     s3 = replace (sym s2) s1

, finiteness of |NonEmpty|

> -- finiteNonEmpty : {t : Nat} -> {n : Nat} -> 
> --                  (x : State t) -> (y : Ctrl t x) -> 
> --                  Finite (SeqDecProbsCoreAssumptions.NonEmpty (step t x y))
> SeqDecProbsHelpers.finiteNonEmpty {t} {n} x y = ListProperties.finiteNonEmpty (step t x y)

and, finally, finiteness of controls

> -- finiteCtrl : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Ctrl t x) 
> SeqDecProbsHelpers.finiteCtrl _ = finiteLeftAheadRight
> %freeze SeqDecProbsHelpers.finiteCtrl

With these results in place, we have

> SeqDecProbsCoreAssumptions.max x v =
>   Opt.max totalPreorderNatLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v)

> SeqDecProbsCoreAssumptions.argmax x v  =
>   Opt.argmax totalPreorderNatLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v)

> SeqDecProbsCoreAssumptions.maxSpec x v =
>   Opt.maxSpec totalPreorderNatLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v)

> SeqDecProbsCoreAssumptions.argmaxSpec x v =
>   Opt.argmaxSpec totalPreorderNatLTE (finiteGoodCtrl x) (cardNotZGoodCtrl x v)



* Decidability of Viable

> dViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Dec (Viable {t} n x)
> dViable {t}  Z    _ = Yes MkUnit
> dViable {t} (S n) x with (decLT (outl x) maxColumn)
>   | (Yes _) = Yes MkUnit
>   | (No  _) = No void



* The computation:

> -- showState : {t : Nat} -> State t -> String
> SeqDecProbsUtils.showState = show

> -- showControl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
> SeqDecProbsUtils.showCtrl = show

> computation : { [STDIO] } Eff ()
> computation =
>   do putStr ("enter number of steps:\n")
>      nSteps <- getNat
>      putStr ("enter initial column:\n")
>      x0 <- getLTB nColumns
>      case (dViable {t = Z} nSteps x0) of
>        (Yes v0) => do putStrLn ("computing optimal policies ...")
>                       ps   <- pure (bi Z nSteps)
>                       putStrLn ("computing optimal controls ...")
>                       mxys <- pure (stateCtrlTrj x0 () v0 ps)
>                       putStrLn (show mxys)
>                       putStrLn ("done!")                       
>        (No _)   => putStrLn ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")

> main : IO ()
> main = run computation

> ---}

-- Local Variables:
-- idris-packages: ("effects")
-- End:
