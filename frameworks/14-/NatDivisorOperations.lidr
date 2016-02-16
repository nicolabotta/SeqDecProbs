> module NatDivisorOperations


> import NatDivisor


> %default total

> %access public export


> ||| Exact integer division
> quotient : (m : Nat) -> (d : Nat) -> d `Divisor` m -> Nat
> quotient _ _ (Element q _) = q 




