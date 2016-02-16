> module NatGCDOperations


> import NatGCD
> import NatDivisor


> %default total

> %access public export


> |||
> gcdDivisorFst : GCD d m n -> d `Divisor` m
> gcdDivisorFst {d} (MkGCD dDm dDn dG) = dDm

> |||
> gcdDivisorSnd : GCD d m n -> d `Divisor` n
> gcdDivisorSnd {d} (MkGCD dDm dDn dG) = dDn

> |||
> gcdDivisorGreatest : GCD d m n -> ((d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d)
> gcdDivisorGreatest {d} (MkGCD dDm dDn dG) = dG


