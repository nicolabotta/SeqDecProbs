> module FractionOperations


> import Fraction
> import PNat


> %default total


> ||| The numerator of a fraction
> num : Fraction -> Nat
> num = fst
> -- %freeze num

> ||| The denominator of a fraction
> den : Fraction -> Nat
> den = nat . snd
> -- %freeze den

> ||| Every natural number is a fraction
> fromNat : Nat -> Fraction
> fromNat n = (n, Element (S Z) MkIsSucc)
> -- %freeze fromNat

> ||| Fraction addition
> plus : Fraction -> Fraction -> Fraction
> plus (n1, d1) (n2, d2) = (n1 * (nat d2) + n2 * (nat d1), d1 * d2)
> -- %freeze plus

> ||| Fraction multiplication
> mult : Fraction -> Fraction -> Fraction
> mult (n1, d1) (n2, d2) = (n1 * n2, d1 * d2)
> -- %freeze mult

