> module FiniteState


> import BoundedNat.Blt
> import DynamicProgramming.S1101_Context

> %default total


# Finite state context extensions:

> nX : Nat

> index : X -> Blt nX

> xedni : Blt nX -> X

> IndexSpec : (x : X) -> x = xedni (index x)

> XedniSpec : (i : Blt nX) -> i = index (xedni i)


