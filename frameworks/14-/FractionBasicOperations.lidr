> module FractionBasicOperations

> import Fraction
> import PNat
> import PNatOperations
> import NatPositive

> %default total
> %access public export


> ||| The numerator of a fraction
> num : Fraction -> Nat
> num = fst


> ||| The denominator of a fraction
> den : Fraction -> Nat
> den = toNat . snd


> ||| Every natural number is a fraction
> fromNat : Nat -> Fraction
> fromNat n = (n, Element (S Z) MkPositive)


> ||| Fraction addition
> plus : Fraction -> Fraction -> Fraction
> plus (n1, d1) (n2, d2) = (n1 * (toNat d2) + n2 * (toNat d1), d1 * d2)


> ||| Fraction multiplication
> mult : Fraction -> Fraction -> Fraction
> mult (n1, d1) (n2, d2) = (n1 * n2, d1 * d2)


> ||| Fraction upscaling
> upscale : Fraction -> PNat -> Fraction
> upscale (m, d) e = (m * (toNat e), d * e)




