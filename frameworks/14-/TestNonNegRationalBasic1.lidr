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
> x  = fromFraction (1, Element 3 MkPositive) 

> y  : NonNegRational
> y  = fromFraction (1, Element 3 MkPositive) 

> z  : NonNegRational
> z  = fromFraction (1, Element 3 MkPositive) 

> xs : List NonNegRational
> xs = [x, y, z]

> sxs : sum xs = fromFraction (1, Element 1 MkPositive) 
> sxs = Refl

