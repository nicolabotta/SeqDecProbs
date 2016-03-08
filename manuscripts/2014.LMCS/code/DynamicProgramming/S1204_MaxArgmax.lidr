> module MaxArgmax

> import Data.So

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability


> %default total

> %access public export


> max : (n : Nat) ->
>       (x : State t) ->
>       (r : So (reachable x)) ->
>       (v : So (viable (S n) x)) ->
>       (f : (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))-> Double) ->
>       Double


> argmax : (n : Nat) ->
>          (x : State t) ->
>          (r : So (reachable x)) ->
>          (v : So (viable (S n) x)) ->
>          (f : (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))-> Double) ->
>          (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))


> maxSpec : (n : Nat) ->
>           (x : State t) ->
>           (r : So (reachable x)) ->
>           (v : So (viable (S n) x)) ->
>           (f : (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))-> Double) ->
>           (yv : (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))) ->
>           So (f yv <= max n x r v f)

-- > maxSpec : (n : Nat) ->
-- >           (x : State t) ->
-- >           (r : So (reachable x)) ->
-- >           (v : So (viable (S n) x)) ->
-- >           (f : (y : Ctrl t x ** So (viable n (step t x y)))-> Double) ->
-- >           (y : Ctrl t x) ->
-- >           (q : So (viable n (step t x y))) ->
-- >           So (f (y ** q) <= max n x r v f)


> argmaxSpec : (n : Nat) ->
>              (x : State t) ->
>              (r : So (reachable x)) ->
>              (v : So (viable (S n) x)) ->
>              (f : (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))-> Double) ->
>              So (f (argmax n x r v f) == max n x r v f)
