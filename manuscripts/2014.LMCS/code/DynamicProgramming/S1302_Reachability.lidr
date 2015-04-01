> module Reachability


> import Util.VectExtensions1
> import DynamicProgramming.S1301_Context


> %default total
  

> reachable : X t -> Bool

> Reachable : X t -> Type
> Reachable x = so (reachable x)

> reachableSpec0  :  (x : X Z) -> Reachable x
> reachableSpec1  :  (x : X t) -> Reachable x -> (y : Y t x) -> 
>                    (x' : X (S t)) -> so (x' `MisIn` (step t x y)) -> Reachable x'
> reachableSpec2  :  (x' : X (S t)) -> Reachable x' ->
>                    (x : X t ** (  Reachable x , 
>                                   (y : Y t x ** so (x' `MisIn` (step t x y)))))


> {-                                                                 
> XR : Nat -> Type
> XR t = (x : X t ** so (reachable x))

> XPred : X t -> X (S t) -> Type
> XPred {t = t} x x' = (y : Y t x ** so (x' `MisIn` (step t x y)))

> reachableSpec1'  :  (xr : XR t) ->
>                     (x' : X (S t)) ->
>                     XPred (outl xr) x' ->
>                     XR (S t)

> reachableSpec2'  :  (x'r : XR (S t)) -> (xr : XR t ** XPred (outl xr) (outl x'r))
> -}
