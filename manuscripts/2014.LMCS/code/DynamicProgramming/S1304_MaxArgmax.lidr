> module MaxArgmax


> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1302_Viability
> import DynamicProgramming.S1303_OptimalPolicies


> max : (n : Nat) ->
>       (x : X t) -> 
>       (r : so (reachable x)) -> 
>       (v : so (viable (S n) x)) ->
>       (f : (y : Y t x ** so (feasible n x y))-> Float) -> 
>       Float


> argmax : (n : Nat) ->
>          (x : X t) -> 
>          (r : so (reachable x)) -> 
>          (v : so (viable (S n) x)) ->
>          (f : (y : Y t x ** so (feasible n x y))-> Float) -> 
>          (y : Y t x ** so (feasible n x y))


> maxSpec : (n : Nat) -> 
>           (x : X t) ->
>           (r : so (reachable {t} x)) -> 
>           (v : so (viable {t} (S n) x)) ->
>           (f : (y : Y t x ** so (feasible n x y))-> Float) -> 
>           (yv : (y : Y t x ** so (feasible n x y))) ->
>           so (f yv <= max n x r v f)


> argmaxSpec : (n : Nat) -> 
>              (x : X t) ->
>              (r : so (reachable x)) -> 
>              (v : so (viable (S n) x)) ->
>              (f : (y : Y t x ** so (feasible {t = t} n x y))-> Float) -> 
>              so (f (argmax n x r v f) == max n x r v f)
