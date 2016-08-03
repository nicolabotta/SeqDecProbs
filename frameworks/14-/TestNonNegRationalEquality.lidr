> module Main

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import Fraction
> import FractionPredicates
> import PNat
> import PNatOperations
> import PNatProperties
> import NatPositive

> %default total
> %auto_implicits off


> f1  : Fraction
> f1  = (1, Element 8 MkPositive)
> z1  : NonNegRational
> z1  = fromFraction f1

> f2  : Fraction
> f2  = (3, Element 24 MkPositive)
> z2  : NonNegRational
> z2  = fromFraction f2

> z1EQz2 : z1 = z2
> z1EQz2 = fromFractionEqLemma f1 f2 Refl

