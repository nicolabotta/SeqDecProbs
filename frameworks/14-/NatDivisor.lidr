> module NatDivisor

> %default total


> Divisor : (m : Nat) -> (n : Nat) -> Type
> Divisor m n = Exists (\ q => m * q = n)

