> module Main

> import NatGCD
> import NatGCDOperations
> import NatGCDProperties
> import NatGCDEuclid
> import NatDivisor
> import NatDivisorOperations

> %default total

> m : Nat
> n : Nat

> d : Nat
> d = getWitness (euclidGCD m n)

> prf : GCD Main.d Main.m Main.n
> prf = getProof (euclidGCD m n)

> dDm : Main.d `Divisor` Main.m
> dDm = gcdDivisorFst prf

> dDn : Main.d `Divisor` Main.n
> dDn = gcdDivisorSnd prf

> m' : Nat
> m' = quotient Main.m Main.d Main.dDm

> n' : Nat
> n' = quotient Main.n Main.d Main.dDn

> m = 42449
> n = 6776

> main : IO ()               
> main = do putStrLn (show d)
>           -- putStrLn (show m')

