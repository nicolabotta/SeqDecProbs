> module NatOperations


> import NatPredicates


> %default total


> %hide (-)


Infix minus

> public (-) : Nat -> Nat -> Nat
> (-) = minus


Divisor operations:

> public divBy : (d : Nat) -> (m : Nat) -> d `Divisor` m -> Nat
> divBy d m (Evidence q prf) = q 





