> module NatOperations


> import NatPredicates


> %default total


> %hide (-)


Infix minus

> public (-) : Nat -> Nat -> Nat
> (-) = minus


Division:

> public quotient : (m : Nat) -> (d : Nat) -> d `Divisor` m -> Nat
> quotient _ _ (Evidence q _) = q 




