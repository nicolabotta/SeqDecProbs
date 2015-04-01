> module MaxArgmax


> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability


> %default total


> max : (n : Nat) ->
>       (x : X t) -> 
>       (r : so (reachable x)) -> 
>       (v : so (viable (S n) x)) ->
>       (f : (y : Y t x ** so (viable {t = S t} n (step t x y)))-> Float) -> 
>       Float


> argmax : (n : Nat) ->
>          (x : X t) -> 
>          (r : so (reachable x)) -> 
>          (v : so (viable (S n) x)) ->
>          (f : (y : Y t x ** so (viable {t = S t} n (step t x y)))-> Float) -> 
>          (y : Y t x ** so (viable {t = S t} n (step t x y)))


> maxSpec : (n : Nat) -> 
>           (x : X t) ->
>           (r : so (reachable x)) -> 
>           (v : so (viable (S n) x)) ->
>           (f : (y : Y t x ** so (viable {t = S t} n (step t x y)))-> Float) -> 
>           (yv : (y : Y t x ** so (viable {t = S t} n (step t x y)))) ->
>           so (f yv <= max n x r v f)

-- > maxSpec : (n : Nat) -> 
-- >           (x : X t) ->
-- >           (r : so (reachable x)) -> 
-- >           (v : so (viable (S n) x)) ->
-- >           (f : (y : Y t x ** so (viable n (step t x y)))-> Float) -> 
-- >           (y : Y t x) -> 
-- >           (q : so (viable n (step t x y))) ->
-- >           so (f (y ** q) <= max n x r v f)


> argmaxSpec : (n : Nat) -> 
>              (x : X t) ->
>              (r : so (reachable x)) -> 
>              (v : so (viable (S n) x)) ->
>              (f : (y : Y t x ** so (viable {t = S t} n (step t x y)))-> Float) -> 
>              so (f (argmax n x r v f) == max n x r v f)
