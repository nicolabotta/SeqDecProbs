> module NatDivisor

> %default total


> Divisor : (m : Nat) -> (n : Nat) -> Type
> Divisor m n = Subset Nat (\ q => m * q = n)

