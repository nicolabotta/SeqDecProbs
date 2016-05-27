> module NonNegRationalPredicates

> import NonNegRational
> import NonNegRationalBasicOperations
> import Fraction
> import FractionPredicates

> %default total
> %access public export
> %auto_implicits off


> ||| Proofs that `x` is less than or equal to `y`                                                                          
> ||| @ x the smaller number                                                                                                
> ||| @ y the larger number
> LTE : (x, y : NonNegRational) -> Type
> LTE x y = FractionPredicates.LTE (toFraction x) (toFraction y)





