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


> dz1 : PNat
> dz1 = Element (S 7) (MkPositive {n = 7})
> f1  : Fraction
> f1  = (1, dz1)
> z1  : NonNegRational
> z1  = fromFraction f1

> dz2 : PNat
> dz2 = Element (S 23) (MkPositive {n = 23})
> f2  : Fraction
> f2  = (3, dz2)
> z2  : NonNegRational
> z2  = fromFraction f2

> f1Eqf2 : f1 `Eq` f2
> f1Eqf2 = Refl

> %freeze fromFraction

> z1EQz2 : z1 = z2
> z1EQz2 = fromFractionEqLemma f1 f2 f1Eqf2

