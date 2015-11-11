> module NatDivisorOperations


> import NatDivisor


> %default total


> ||| Exact integer division
> public quotient : (m : Nat) -> (d : Nat) -> d `Divisor` m -> Nat
> quotient _ _ (Evidence q _) = q 




