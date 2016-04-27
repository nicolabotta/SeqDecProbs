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
> import SeqDecProbsCoreUtils

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
> import SingletonProperties
> import Opt
> import TotalPreorder
> import EffectException
> import EffectStdIO
> import FinOperations
> import PairsOperations

> %default total
> %auto_implicits off


The possibly simplest "cylinder" problem. |M| is the identity monad, the
state space is constant and we can move to the left, ahead or to the
right as we wish.



* The monad M (Identity):


** M is a monad:

> SeqDecProbsCoreAssumptions.M = Identity
> SeqDecProbsCoreAssumptions.fmap = map
> SeqDecProbsCoreAssumptions.ret = return
> SeqDecProbsCoreAssumptions.bind = (>>=)


** M is a container monad:

> SeqDecProbsCoreAssumptions.Elem = IdentityOperations.Elem
> SeqDecProbsCoreAssumptions.All P = P . unwrap
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

*** Controls are finite:

> fCtrl : {t : Nat} -> {x : State t} -> Finite (Ctrl t x)
> fCtrl = finiteLeftAheadRight
> %freeze fCtrl


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
> SeqDecProbsCoreAssumptions.viableSpec1 x v = MkSigma Left ()

> -- Reachable : State t' -> Type
> SeqDecProbsCoreAssumptions.Reachable x' = Unit

> -- reachableSpec1 : (x : State t) -> Reachable {t' = t} x -> (y : Ctrl t x) -> All (Reachable {t' = S t}) (step t x y)
> SeqDecProbsCoreAssumptions.reachableSpec1 x r y = ()



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
>        Finite1 P -> (mx : Identity (State t)) -> Finite (All P mx)
> fAll f1P (Id x) = f1P x

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
> dViable n x = Yes ()



* The computation:

> -- showState : {t : Nat} -> State t -> String
> SeqDecProbsCoreUtils.showState = show

> -- showControl : {t : Nat} -> {x : State t} -> Ctrl t x -> String
> SeqDecProbsCoreUtils.showCtrl = show

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
