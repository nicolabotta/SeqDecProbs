> module Main


> import NonNegRational
> import NonNegRationalOperations
> import NonNegRationalProperties
> import Fraction
> import FractionOperations
> import FractionProperties
> import PNat
> import PNatOperations
> import PNatProperties
> import NatProperties


> %default total


> zLTs : {m : Nat} -> LT Z (S m)
> zLTs {m} = ltZS m


> x : NonNegQ
> x = fromFraction (7, fromNat 3 zLTs) 

> y : NonNegQ
> y = fromFraction (28, fromNat 8 zLTs)


> z : NonNegQ
> z = x `plus` y
