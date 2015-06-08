> module MaxArgmax

> import Data.So

> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1302_Viability
> import DynamicProgramming.S1303_OptimalPolicies
> import DynamicProgramming.S1302_Feasibility


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
>          (f : (y : Y t x ** So (feasible n x y))-> Float) -> 
>          (y : Y t x ** So (feasible n x y))


> maxSpec : (n : Nat) -> 
>           (x : X t) ->
>           (r : So (reachable {t} x)) -> 
>           (v : So (viable {t} (S n) x)) ->
>           (f : (y : Y t x ** So (feasible n x y))-> Float) -> 
>           (yv : (y : Y t x ** So (feasible n x y))) ->
>           So (f yv <= max n x r v f)


> argmaxSpec : (n : Nat) -> 
>              (x : X t) ->
>              (r : So (reachable x)) -> 
>              (v : So (viable (S n) x)) ->
>              (f : (y : Y t x ** So (feasible {t = t} n x y))-> Float) -> 
>              So (f (argmax n x r v f) == max n x r v f)
