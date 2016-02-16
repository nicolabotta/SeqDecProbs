> module NonNegRationalOperations


> import NonNegRational
> import Fraction
> import FractionOperations
> import FractionProperties
> import PairsOperations
> -- import Sigma


> %default total

> %access public export


> ||| 
> toFraction : NonNegRational -> Fraction
> toFraction = getWitness
> -- %freeze toFraction


> ||| 
> fromFraction : Fraction -> NonNegRational
> fromFraction x = Element (normalize x) (normalNormalize x)
> -- %freeze toFraction


> ||| The numerator of a non-negative rational
> num : NonNegRational -> Nat
> num = num . toFraction
> -- %freeze num


> ||| The denominator of a non-negative rational
> den : NonNegRational -> Nat
> den = den . toFraction 
> -- %freeze den


> ||| Every natural number is a non-negative rational
> fromNat : (n : Nat) -> NonNegRational
> fromNat = fromFraction . fromNat
> -- %freeze fromNat


> ||| Addition of non-negarive rational numbers
> plus : NonNegRational -> NonNegRational -> NonNegRational
> plus x y = fromFraction (toFraction x + toFraction y)
> -- %freeze plus


> ||| Multiplication of non-negarive rational numbers
> mult : NonNegRational -> NonNegRational -> NonNegRational
> mult x y = fromFraction (toFraction x * toFraction y)
> -- %freeze mult

