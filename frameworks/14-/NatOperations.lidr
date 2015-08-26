> module NatOperations


> import NatPredicates


> %default total


Divisor operations:

> divBy : (d : Nat) -> (m : Nat) -> d `Divisor` m -> Nat
> divBy d m (Evidence q prf) = q 





