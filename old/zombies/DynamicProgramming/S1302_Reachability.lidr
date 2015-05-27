> module Reachability


> import Data.So

> import Util.VectExtensions1
> import DynamicProgramming.S1301_Context


> %default total
  

> reachable : X t -> Bool

> reachableSpec0 : (x : X Z) -> So (reachable x)

> reachableSpec1 : (x : X t) ->
>                  So (reachable x) ->
>                  (y : Y t x) ->
>                  (x' : X (S t)) ->
>                  So (x' `MisIn` (step t x y)) ->
>                  So (reachable x')

> reachableSpec2 : (x' : X (S t)) -> 
>                  So (reachable x') ->
>                  (x : X t ** (y : Y t x ** (So (reachable x), So (x' `MisIn` (step t x y)))))
