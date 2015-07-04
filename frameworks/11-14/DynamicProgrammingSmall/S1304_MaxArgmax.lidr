> module MaxArgmax

> import Data.So

> import DynamicProgrammingSmall.S1301_Context
> import DynamicProgrammingSmall.S1302_Reachability
> import DynamicProgrammingSmall.S1302_Viability
> import DynamicProgrammingSmall.S1302_Feasibility


> max : (n : Nat) ->
>       (x : X t) -> 
>       (r : So (reachable x)) -> 
>       (v : So (viable (S n) x)) ->
>       (f : (y : Y t x ** So (feasible n x y))-> Float) -> 
>       Float


> argmax : (n : Nat) ->
>          (x : X t) -> 
>          (r : So (reachable x)) -> 
>          (v : So (viable (S n) x)) ->
>          (f : (y : Y t x ** So (feasible {t = t} n x y))-> Float) -> 
>          (y : Y t x ** So (feasible {t = t} n x y))


