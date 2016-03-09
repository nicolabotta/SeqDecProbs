> import NonNegRational2
> import Fraction
> import NatProperties
> %default total

> zLTs : {m : Nat} -> LT Z (S m)
> zLTs {m} = ltZS m

> x' : Fraction
> x' = (7, fromNat 3 zLTs)
