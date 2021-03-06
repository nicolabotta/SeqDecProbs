> module MaxArgmax

> import Data.So

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability


> %default total


> max : (n : Nat) ->
>       (x : X t) -> 
>       (r : So (reachable x)) -> 
>       (v : So (viable (S n) x)) ->
>       (f : (y : Y t x ** So (viable n (step t x y)))-> Float) -> 
>       Float


> argmax : (n : Nat) ->
>          (x : X t) -> 
>          (r : So (reachable x)) -> 
>          (v : So (viable (S n) x)) ->
>          (f : (y : Y t x ** So (viable n (step t x y)))-> Float) -> 
>          (y : Y t x ** So (viable n (step t x y)))


> maxSpec : (n : Nat) -> 
>           (x : X t) ->
>           (r : So (reachable x)) -> 
>           (v : So (viable (S n) x)) ->
>           (f : (y : Y t x ** So (viable {t = S t} n (step t x y)))-> Float) -> 
>           (yv : (y : Y t x ** So (viable {t = S t} n (step t x y)))) ->
>           So (f yv <= max n x r v f)

-- > maxSpec : (n : Nat) -> 
-- >           (x : X t) ->
-- >           (r : So (reachable x)) -> 
-- >           (v : So (viable (S n) x)) ->
-- >           (f : (y : Y t x ** So (viable n (step t x y)))-> Float) -> 
-- >           (y : Y t x) -> 
-- >           (q : So (viable n (step t x y))) ->
-- >           So (f (y ** q) <= max n x r v f)


> argmaxSpec : (n : Nat) -> 
>              (x : X t) ->
>              (r : So (reachable x)) -> 
>              (v : So (viable (S n) x)) ->
>              (f : (y : Y t x ** So (viable {t = S t} n (step t x y)))-> Float) -> 
>              So (f (argmax n x r v f) == max n x r v f)
