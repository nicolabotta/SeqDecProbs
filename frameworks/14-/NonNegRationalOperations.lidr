> module NonNegRationalOperations


> import NonNegRational
> import Fraction
> import FractionOperations
> import FractionProperties
> import FractionReduction
> import FractionReductionOperations
> import FractionReductionProperties
> import PNat
> import NatCoprime
> import NatCoprimeProperties
> import NatGCD
> import NatGCDEuclid


> %default total


> ||| 
> toFraction : NonNegQ -> Fraction
> toFraction = getWitness
> -- %freeze toFraction

> {-
> ||| 
> fromFraction : Fraction -> NonNegQ
> fromFraction x = Element (reduce x) (reduceReduces x)
> -- %freeze toFraction
> -}

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
> -- fromNat = fromFraction . fromNat
> fromNat n = Element (fromNat n) (fromNatReduced n)
> -- %freeze fromNat


> ||| Addition of non-negarive rational numbers
> plus : NonNegQ -> NonNegQ -> NonNegQ
> plus x' y' = let x   =  toFraction x' in
>              let y   =  toFraction y' in
>              reduce (x + y)
> -- %freeze plus


> ||| Multiplication of non-negarive rational numbers
> mult : NonNegQ -> NonNegQ -> NonNegQ
> mult x' y' = let x   =  toFraction x' in
>              let y   =  toFraction y' in
>              reduce (x * y)
> -- %freeze mult


> {-

> ---}
