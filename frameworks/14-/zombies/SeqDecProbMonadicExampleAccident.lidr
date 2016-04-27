> module SeqDecProbMonadicTheoryRVExampleAccident


> import Data.List
> import Data.List.Quantifiers


> import SeqDecProbMonadicTheoryRV as Theory
> import ListOperations
> import Prop


> %default total


** M is a monad:

> Theory.M = List

> Theory.fmap = map

> Theory.ret = return
> -- %freeze ret

> Theory.bind = (>>=)
> -- %freeze bind


** M is a container monad:

> Theory.Elem = Data.List.Elem

> Theory.All = Data.List.Quantifiers.All

> Theory.tagElem = ListOperations.tagElem
> -- %freeze tagElem

> Theory.containerMonadSpec3 {A} {P} _  Nil      _ q = absurd q
> Theory.containerMonadSpec3 {A} {P} x (x :: ys) (px :: apys) (Here) = px
> Theory.containerMonadSpec3 {A} {P} x (y :: ys) (py :: apys) (There p) = containerMonadSpec3 x ys apys p
> -- %freeze containerMonadSpec3


** 

> namespace Step0
>   data State = AccidentCarBurning
>   namespace AccidentCarBurning
>     data Ctrl  =  DoNothing | CallHelp | Rescue

> namespace Step1
>   data State = CarBurning | HelpComesCarBurning | ChildAlive
>   namespace CarBurning
>     data Ctrl = DoNothing | Rescue
>   namespace HelpComesCarBurning
>     data Ctrl = Rescue
>   namespace ChildAlive
>     data Ctrl = DoNothing

> namespace OtherSteps
>   data State = ChildAlive | ChildDead
>   data Ctrl = DoNothing


> -- X : (t : Nat) -> Type
> Theory.X       Z   = Step0.State
> Theory.X    (S Z)  = Step1.State
> Theory.X (S (S n)) = OtherSteps.State
 
> -- Theory.Y : (t : Nat) -> (x : X t) -> Type
> Theory.Y       Z   Step0.AccidentCarBurning   = Step0.AccidentCarBurning.Ctrl
> Theory.Y    (S Z)  Step1.CarBurning           = Step1.CarBurning.Ctrl
> Theory.Y    (S Z)  Step1.HelpComesCarBurning  = Step1.HelpComesCarBurning.Ctrl
> Theory.Y    (S Z)  Step1.ChildAlive           = Step1.ChildAlive.Ctrl
> Theory.Y (S (S n)) OtherSteps.x               = OtherSteps.Ctrl

> Theory.step       Z   Step0.AccidentCarBurning  Step0.AccidentCarBurning.DoNothing   = [Step1.CarBurning]
> Theory.step       Z   Step0.AccidentCarBurning  Step0.AccidentCarBurning.CallHelp    = [Step1.HelpComesCarBurning]
> Theory.step       Z   Step0.AccidentCarBurning  Step0.AccidentCarBurning.Rescue      = [Step1.ChildAlive]
> Theory.step    (S Z)  Step1.CarBurning          Step1.CarBurning.DoNothing           = [OtherSteps.ChildDead]
> Theory.step    (S Z)  Step1.CarBurning          Step1.CarBurning.Rescue              = [OtherSteps.ChildDead]
> Theory.step    (S Z)  Step1.HelpComesCarBurning Step1.HelpComesCarBurning.Rescue     = [OtherSteps.ChildDead,OtherSteps.ChildAlive]
> Theory.step    (S Z)  Step1.ChildAlive          Step1.ChildAlive.DoNothing           = [OtherSteps.ChildAlive]
> Theory.step (S (S n)) OtherSteps.x              OtherSteps.y                         = [OtherSteps.x]

> Theory.reward    Z  _ _ _                     = Z
> Theory.reward (S Z) _ _ OtherSteps.ChildAlive = 100
> Theory.reward    _  _ _ _                     = Z

> {-

> ---}
