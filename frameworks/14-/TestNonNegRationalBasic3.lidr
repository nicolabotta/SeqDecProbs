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
> -- x  = fromFraction (2067, Element 616 (MkPositive {n = 615}))
> x  = fromFraction (2067, Element 616 MkPositive)
