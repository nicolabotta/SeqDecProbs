> module Main

> import Decidable.Order

> import Data.Fin
> import Data.Vect
> import Data.So
> import Control.Monad.Identity
> import Control.Isomorphism
> import Effects
> import Effect.Exception
> import Effect.StdIO
> import Syntax.PreorderReasoning

> import SeqDecProbsCoreAssumptions
> import SeqDecProbsCoreTheory
> import SeqDecProbsUtils
> import SeqDecProbsHelpers
> import SeqDecProbsTabulatedBackwardsInduction

> import IdentityOperations
> import IdentityProperties
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
> import Opt
> import TotalPreorder
> import EffectException
> import EffectStdIO
> import FinOperations
> import PairsOperations

> %default total
> %auto_implicits off


> -- %logging 5

A tabulated version of "SeqDecProbsExample1.lidr".



* The monad M (Identity):


** M is a monad:

> SeqDecProbsCoreAssumptions.M = Identity
> SeqDecProbsCoreAssumptions.fmap = map
> SeqDecProbsCoreAssumptions.ret = return
> SeqDecProbsCoreAssumptions.bind = (>>=)


** M is a container monad:

> SeqDecProbsCoreAssumptions.Elem = IdentityOperations.Elem
> SeqDecProbsCoreAssumptions.NonEmpty = IdentityOperations.NonEmpty
> SeqDecProbsCoreAssumptions.All P = P . unwrap
> SeqDecProbsCoreAssumptions.elemNonEmptySpec0 = IdentityProperties.elemNonEmptySpec0
> SeqDecProbsCoreAssumptions.elemNonEmptySpec1 = IdentityProperties.elemNonEmptySpec1
> SeqDecProbsCoreAssumptions.tagElem = IdentityOperations.tagElem
> SeqDecProbsCoreAssumptions.containerMonadSpec3 {A} {P} a1 (Id a2) pa2 a1eqa2 =
>   replace (sym a1eqa2) pa2


** M is measurable:

> SeqDecProbsCoreAssumptions.meas (Id x) = x

> SeqDecProbsCoreAssumptions.measMon f g prf (Id x) = prf x



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
>   Id (MkSigma maxColumn (ltIdS maxColumn))
> SeqDecProbsCoreAssumptions.step t (MkSigma (S n) prf) Left =
>   Id (MkSigma n (ltLemma1 n nColumns prf))
> SeqDecProbsCoreAssumptions.step t (MkSigma n prf) Ahead =
>   Id (MkSigma n prf)
> SeqDecProbsCoreAssumptions.step t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = Id (MkSigma (S n) (LTESucc p))
>   | (No contra) = Id (MkSigma  Z    (LTESucc LTEZero))


** Reward function:

> SeqDecProbsCoreAssumptions.reward t x y (MkSigma c _) =
>   if c == Z
>   then (S Z)
>   else if (S c) == nColumns
>        then (S (S Z))
>        else Z



* Viable and Reachable

> -- Viable : (n : Nat) -> State t -> Type
> SeqDecProbsCoreAssumptions.Viable n x =  Unit

> -- viableSpec1 : (x : State t) -> Viable (S n) x -> GoodCtrl t x n
> -- SeqDecProbsCoreAssumptions.viableSpec1 x v = MkSigma Left ()
> SeqDecProbsCoreAssumptions.viableSpec1 {t} x v = MkSigma Left (nonEmptyLemma (step t x Left), ())

> -- Reachable : State t' -> Type
> SeqDecProbsCoreAssumptions.Reachable x' = Unit

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (step t x y)
> SeqDecProbsCoreAssumptions.reachableSpec1 x r y = ()



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
> SeqDecProbsHelpers.finiteAll = IdentityProperties.finiteAll

, finiteness of |Viable|

> -- finiteViable : {t : Nat} -> {n : Nat} -> 
> --                (x : State t) -> Finite (Viable {t} n x)
> SeqDecProbsHelpers.finiteViable _ = finiteUnit

, finiteness of |NonEmpty|

> -- finiteNonEmpty : {t : Nat} -> {n : Nat} -> 
> --                  (x : State t) -> (y : Ctrl t x) -> 
> --                  Finite (SeqDecProbsCoreAssumptions.NonEmpty (step t x y))
> SeqDecProbsHelpers.finiteNonEmpty {t} {n} x y = IdentityProperties.finiteNonEmpty (step t x y)

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



* Finiteness of |State|, decidability of |Viable| and |Reachable|

> SeqDecProbsTabulatedBackwardsInduction.fState t = finiteLTB _

> -- dReachable : {t' : Nat} -> (x' : X t') -> Dec (Reachable x')
> SeqDecProbsTabulatedBackwardsInduction.dReachable {t'} x' = Yes ()

> -- dViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Dec (Viable {t} n x)
> SeqDecProbsTabulatedBackwardsInduction.dViable {t} n x = Yes ()



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
>                       ps   <- pure (ttrbi Z nSteps)
>                       putStrLn ("computing optimal controls ...")
>                       mxys <- pure (stateCtrlTrj x0 () v0 ps)
>                       putStrLn (show mxys)
>                       putStrLn ("done!")                       
>        (No _)   => putStrLn ("initial column non viable for " ++ cast {from = Int} (cast nSteps) ++ " steps")

> main : IO ()
> main = run computation

> {-

> ---}

-- Local Variables:
-- idris-packages: ("effects")
-- End:
