> module Main

> import SimpleProb
> import SimpleProbBasicOperations
> import SimpleProbBasicProperties
> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import Fraction
> import PNat
> import NatPositive
> import ListOperations

> %default total
> %auto_implicits off

> oo2  : NonNegRational
> oo2  = fromFraction (1, Element 2 MkPositive) 

> oo3  : NonNegRational
> oo3  = fromFraction (1, Element 3 MkPositive) 

> sp : SimpleProb Nat
> sp = MkSimpleProb [(0, oo3), (2, oo3), (5, oo3)] Refl





