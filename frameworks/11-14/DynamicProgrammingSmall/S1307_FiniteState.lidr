> module FiniteState


> import Data.So

> import BoundedNat.Blt

> import DynamicProgrammingSmall.S1301_Context
> import DynamicProgrammingSmall.S1302_Reachability
> import DynamicProgrammingSmall.S1302_Viability

> %default total


> nX : (t : Nat) -> (n : Nat) -> Nat 


> index : (n : Nat) ->
>         (x : X t ** (So (reachable x), So (viable n x))) -> 
>         Blt (nX t n)

> xedni : (n : Nat) ->
>         Blt (nX t n) -> 
>         (x : X t ** (So (reachable x), So (viable n x)))


