> module FiniteState

> import Data.So

> import BoundedNat.Blt

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability

> %default total

At the moment we need this only for implementing the linear version of
backwars induction. We will reconsider the case in which |X| is finite
later (maybe when we consider the additional assumptions we need to
restrict the class of functions that can be passed to |argamax| and make
|argmax| total).


> nX : (t : Nat) -> (n : Nat) -> Nat 

|nX t n| is the cardinality of the set

   { x `in` X t | x is reachable and is viable for n steps }

> index : (n : Nat) ->
>         (x : X t ** (So (reachable x), So (viable n x))) -> 
>         Blt (nX t n)

> xedni : (n : Nat) ->
>         Blt (nX t n) -> 
>         (x : X t ** (So (reachable x), So (viable n x)))


> IndexSpec : (n' : Nat) ->
>             (xrv : (x : X t ** (So (reachable {t} x), So (viable {t} n' x)))) -> 
>             xrv = xedni n' (index n' xrv)

> XedniSpec : (n : Nat) ->
>             (i : Blt (nX t n)) -> 
>             i = index n (xedni n i)


