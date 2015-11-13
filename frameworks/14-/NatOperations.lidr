> module NatOperations


> import NatPredicates


> %default total


> %hide (-)


Predecessor:

> public pred : (n : Nat) -> Z `LT` n -> Nat
> pred  Z    prf = absurd prf
> pred (S m) _   = m


Infix minus:

> public (-) : Nat -> Nat -> Nat
> (-) = minus


Division:

> public quotient : (m : Nat) -> (d : Nat) -> d `Divisor` m -> Nat
> quotient _ _ (Evidence q _) = q 




