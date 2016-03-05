> module MaxArgmax

> import Data.So

> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1302_Viability
> import DynamicProgramming.S1303_OptimalPolicies


> max : (n : Nat) ->
>       (x : State t) ->
>       (r : Reachable x) ->
>       (v : Viable (S n) x) ->
>       (f : (y : Ctrl t x ** So (Mfeasible n x y))-> Double) ->
>       Double


> argmax : (n : Nat) ->
>          (x : State t) ->
>          (r : Reachable x) ->
>          (v : Viable (S n) x) ->
>          (f : (y : Ctrl t x ** So (Mfeasible n x y))-> Double) ->
>          (y : Ctrl t x ** So (Mfeasible n x y))


> maxSpec : (n : Nat) ->
>           (x : State t) ->
>           (r : Reachable {t} x) ->
>           (v : Viable {t} (S n) x) ->
>           (f : (y : Ctrl t x ** So (Mfeasible n x y))-> Double) ->
>           (yv : (y : Ctrl t x ** So (Mfeasible n x y))) ->
>           So (f yv <= max n x r v f)


> argmaxSpec : (n : Nat) ->
>              (x : State t) ->
>              (r : Reachable x) ->
>              (v : Viable (S n) x) ->
>              (f : (y : Ctrl t x ** So (Mfeasible {t = t} n x y))-> Double) ->
>              So (f (argmax n x r v f) == max n x r v f)
