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

A tabulated version of "SeqDecProbsExample2.lidr".



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


** M is measurable:

> SeqDecProbsCoreAssumptions.meas = sum

> SeqDecProbsCoreAssumptions.measMon = sumMon



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

> postulate stepLemma1 : {t : Nat} -> 
>                        (x : State t) -> (outl x `LT` maxColumn) -> 
>                        SeqDecProbsCoreAssumptions.NonEmpty (step t x Ahead)


** Reward function:

> SeqDecProbsCoreAssumptions.reward t x y (MkSigma c _) =
>   if c == Z
>   then (S Z)
>   else if (S c) == nColumns
>        then (S (S Z))
>        else Z



* Viable and Reachable

> -- Viable : (n : Nat) -> State t -> Type
> SeqDecProbsCoreAssumptions.Viable n x with (decLT (outl x) maxColumn)
>   | (Yes _) = Unit
>   | (No  _) = Void

> viableLemma : {t : Nat} -> {n : Nat} ->
>               (x : State t) -> 
>               SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) (step t x Ahead)
> viableLemma {t} {n} (MkSigma i prf) with (decLT i maxColumn)
>   | (Yes p) = res where
>     res : SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) [MkSigma i prf]
>     res = v :: Nil where
>       v : Viable {t = S t} n (MkSigma i prf)
>       v with (decLT i maxColumn)
>         | (Yes _) = ()
>         | (No  contra) = void (contra p)
>   | (No  _) = Nil

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
>   all (x :: xs) = () :: (all xs)



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
> SeqDecProbsHelpers.finiteViable {t} {n} x with (decLT (outl x) maxColumn)
>   | (Yes _) = finiteUnit
>   | (No  _) = finiteVoid

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
> dViable {t} n x with (decLT (outl x) maxColumn)
>   | (Yes _) = Yes ()
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
