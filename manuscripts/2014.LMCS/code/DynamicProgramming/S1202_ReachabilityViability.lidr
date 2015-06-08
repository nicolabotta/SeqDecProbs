> module ReachabilityViability

> import Data.So

> import Util.VectExtensions1
> import DynamicProgramming.S1201_Context


> %default total


> reachable       :  State t -> Bool
> Reachable       :  State t -> Type

> Reachable x = So (reachable x)

> reachableSpec0  :  (x : State Z)      -> Reachable x
> reachableSpec1  :  (x : State t)      -> Reachable x ->
>                    (y : Ctrl t x)     -> Reachable (step t x y)
> reachableSpec2  :  (x' : State (S t)) -> Reachable x' ->
>                    (x : State t **    (  Reachable x ,
>                                          (y : Ctrl t x **  x' = step t x y)))

> viable       :  (n : Nat) -> State t -> Bool

> Viable : (n : Nat) -> State t -> Type
> Viable n x = So (viable n x)

> GoodCtrl : (t : Nat) -> (n : Nat) -> State t -> Type
> GoodCtrl t n x = (y : Ctrl t x ** Viable n (step t x y))

> viableSpec0  :  (x : State t) -> Viable Z x
> viableSpec1  :  (x : State t) -> Viable (S n) x -> GoodCtrl t n x
> viableSpec2  :  (x : State t) -> GoodCtrl t n x -> Viable (S n) x
