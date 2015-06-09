> module Reachability

> import Data.So

> import Util.VectExtensions1
> import DynamicProgramming.S1301_Context


> %default total
  

> reachable       :  State t -> Bool

> Reachable : State t -> Type
> Reachable x = So (reachable x)

> reachableSpec0  :  (x : State Z) -> Reachable x
> reachableSpec1  :  (x : State t) -> Reachable x -> (y : Ctrl t x) -> 
>                    (x' : State (S t)) -> So (x' `MisIn` (step t x y)) -> Reachable x'
> reachableSpec2  :  (x' : State (S t)) -> Reachable x' ->
>                    (x : State t ** (Reachable x, (y : Ctrl t x ** So (x' `MisIn` (step t x y)))))

