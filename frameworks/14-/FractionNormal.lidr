> module FractionNormal


> import Fraction
> import FractionOperations
> import NatCoprime
> import Unique
> import NatGCD
> import NatGCDEuclid
> import PNat
> import NatPositive
> import PairsOperations


> %default total

> %access public export


> ||| 
> data Normal : Fraction -> Type where
>   MkNormal  : {x : Fraction} -> Coprime (num x) (den x) -> Normal x

> |||
> NormalUnique : {x : Fraction} -> Unique (Normal x)
> NormalUnique {x} (MkNormal p) (MkNormal q) = cong (CoprimeUnique p q)

