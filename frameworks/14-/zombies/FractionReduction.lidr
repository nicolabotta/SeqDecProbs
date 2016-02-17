> module FractionReduction


> import Fraction
> import FractionOperations
> import NatCoprime
> import Unique
> import NatGCD
> import NatGCDEuclid
> import PNat


> %default total


> ||| 
> data Reduced : Fraction -> Type where
>   MkReduced  : {x : Fraction} -> Coprime (num x) (den x) -> Reduced x

> |||
> ReducedUnique : {x : Fraction} -> Unique (Reduced x)
> ReducedUnique {x} (MkReduced p) (MkReduced q) = cong (CoprimeUnique p q)

