> module NatOperations


> import NatPredicates


> %default total

> %access public export

> %hide (-)


Predecessor:

> pred : (n : Nat) -> Z `LT` n -> Nat
> pred  Z    prf = absurd prf
> pred (S m) _   = m


Infix minus:

> (-) : Nat -> Nat -> Nat
> (-) = minus


Division:

> quotient : (m : Nat) -> (d : Nat) -> d `Divisor` m -> Nat
> quotient _ _ (Evidence q _) = q 




