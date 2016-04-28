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
> import SingletonProperties
> import Opt
> import TotalPreorder
> import EffectException
> import EffectStdIO
> import FinOperations
> import PairsOperations

> %default total
> %auto_implicits off


> -- %logging 5

We reimplement "SeqDecProbsExample1.lidr", this time with |M = List|.



* The monad M (List):


** M is a monad:

> SeqDecProbsCoreAssumptions.M = List
> SeqDecProbsCoreAssumptions.fmap = ListOperations.fmap
> SeqDecProbsCoreAssumptions.ret = ListOperations.ret
> SeqDecProbsCoreAssumptions.bind = ListOperations.bind


** M is a container monad:

> SeqDecProbsCoreAssumptions.Elem = Data.List.Elem
> SeqDecProbsCoreAssumptions.Empty = ListOperations.Empty
> SeqDecProbsCoreAssumptions.All = Data.List.Quantifiers.All
> SeqDecProbsCoreAssumptions.elemEmptySpec0 = ListProperties.elemEmptySpec0
> SeqDecProbsCoreAssumptions.elemEmptySpec1 = ListProperties.elemEmptySpec1
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

*** Controls are finite:

> fCtrl : {t : Nat} -> {x : State t} -> Finite (Ctrl t x)
> fCtrl = finiteLeftAheadRight
> %freeze fCtrl


** Transition function:

> SeqDecProbsCoreAssumptions.step t (MkSigma Z prf) Left =
>   [MkSigma maxColumn (ltIdS maxColumn)]
> SeqDecProbsCoreAssumptions.step t (MkSigma (S n) prf) Left =
>   [MkSigma n (ltLemma1 n nColumns prf)]
> SeqDecProbsCoreAssumptions.step t (MkSigma n prf) Ahead =
>   [MkSigma n prf]
> SeqDecProbsCoreAssumptions.step t (MkSigma n prf) Right with (decLT n maxColumn)
>   | (Yes p)     = [MkSigma (S n) (LTESucc p)]
>   | (No contra) = [MkSigma  Z    (LTESucc LTEZero)]


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
> SeqDecProbsCoreAssumptions.viableSpec1 {t} {n} x _ = MkSigma y s2 where
>   y : Ctrl t x
>   y = Left
>   mx' : List (State (S t))
>   mx' = step t x y 
>   s2  : Good t x n y
>   s2  = all mx' where
>     all : (xs : List (State (S t))) -> SeqDecProbsCoreAssumptions.All (Viable {t = S t} n) xs
>     all Nil = Nil
>     all (x :: xs) = () :: (all xs)

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
that |GoodCtrl t x n| is finite and non-empty for every |t : Nat|, |x :
State t| such that |Viable (S n) x|. If we have finiteness

> fGoodCtrl : {t : Nat} -> {n : Nat} -> 
>             (x : State t) -> Viable {t = t} (S n) x ->
>             Finite (GoodCtrl t x n) 

non-emptiness is straightforward:

> neGoodCtrl : {t : Nat} -> {n : Nat} -> 
>              (x : State t) -> (v : Viable {t = t} (S n) x) ->
>              NonEmpty (fGoodCtrl {t} {n} x v)
> neGoodCtrl {t} {n} x v = nonEmptyLemma {A = GoodCtrl t x n} (fGoodCtrl x v) gy where
>   gy : GoodCtrl t x n 
>   gy = viableSpec1 x v            
 
Thus, the problem is that of implementing |fGoodCtrl|. We already know
that |Ctrl t x| is finite. If we manage to show that for every |y|,
|Good t x n| is also finite, we can apply |finiteSigmaLemma| from
|SigmaProperties| and we are done. We show the result in two steps

> fAll : {t : Nat} -> {P : State t -> Type} ->
>        Finite1 P -> (mx : List (State t)) -> Finite (SeqDecProbsCoreAssumptions.All P mx)
> fAll = finiteAllLemma

and

> fViable : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite (Viable {t} n x)
> fViable _ = finiteSingleton 

> f1Good : {t : Nat} -> {n : Nat} -> (x : State t) -> Finite1 (Good t x n)
> f1Good {t} {n} x y = fAll {t} (fViable {t = S t} {n}) (step t x y)

With |f1Good| we can finally implement |fGoodCtrl|

> fGoodCtrl {t} {n} x v = finiteSigmaLemma0 (fCtrl {t} {x}) (f1Good {t} {n} x)

and |max|, |argmax|, |maxSpec| and |argmaxSpec|:

> SeqDecProbsCoreAssumptions.max x v =
>   Opt.max totalPreorderNatLTE (fGoodCtrl x v) (neGoodCtrl x v)

> SeqDecProbsCoreAssumptions.argmax x v  =
>   Opt.argmax totalPreorderNatLTE (fGoodCtrl x v) (neGoodCtrl x v)

> SeqDecProbsCoreAssumptions.maxSpec x v =
>   Opt.maxSpec totalPreorderNatLTE (fGoodCtrl x v) (neGoodCtrl x v)

> SeqDecProbsCoreAssumptions.argmaxSpec x v =
>   Opt.argmaxSpec totalPreorderNatLTE (fGoodCtrl x v) (neGoodCtrl x v)


* Decidability of Viable

> dViable : {t : Nat} -> (n : Nat) -> (x : State t) -> Dec (Viable {t} n x)
> dViable {t} n x = Yes ()



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

> {-

> ---}

-- Local Variables:
-- idris-packages: ("effects")
-- End:
