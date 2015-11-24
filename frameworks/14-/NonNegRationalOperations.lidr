> module NonNegRationalOperations


> import NonNegRational
> import Fraction
> import FractionOperations
> import FractionProperties


> %default total


> ||| 
> toFraction : NonNegQ -> Fraction
> toFraction = getWitness
> -- %freeze toFraction


> ||| 
> fromFraction : Fraction -> NonNegQ
> fromFraction x = Element (normalize x) (normalNormalize x)
> -- %freeze toFraction


> ||| The numerator of a non-negative rational
> num : NonNegQ -> Nat
> num = num . toFraction
> -- %freeze num


> ||| The denominator of a non-negative rational
> den : NonNegQ -> Nat
> den = den . toFraction 
> -- %freeze den


> ||| Every natural number is a non-negative rational
> fromNat : (n : Nat) -> NonNegQ
> fromNat = fromFraction . fromNat
> -- %freeze fromNat


> ||| Addition of non-negarive rational numbers
> plus : NonNegQ -> NonNegQ -> NonNegQ
> plus x y = fromFraction (toFraction x + toFraction y)
> -- %freeze plus


> ||| Multiplication of non-negarive rational numbers
> mult : NonNegQ -> NonNegQ -> NonNegQ
> mult x y = fromFraction (toFraction x * toFraction y)
> -- %freeze mult

