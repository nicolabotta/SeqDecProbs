> module FiniteState


> import Data.So

> import BoundedNat.Blt

> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1302_Viability

> %default total


> nX : (t : Nat) -> (n : Nat) -> Nat 


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


