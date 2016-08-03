> module Main

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import Fraction
> import PNat
> import NatPositive

> %default total
> %auto_implicits off


> x  : NonNegRational
> x  = fromFraction (1, Element 6 MkPositive) 

> y  : NonNegRational
> y  = fromFraction (2, Element 6 MkPositive) 

> z  : NonNegRational
> z  = fromFraction (3, Element 6 MkPositive) 

> xs : List NonNegRational
> xs = [x, y, z]

> sxs : sum xs = fromFraction (1, Element 1 MkPositive) 
> sxs = Refl

