> module NonNegRational


> import Fraction
> import FractionReduction


> %default total


> ||| Non negative rationals
> NonNegQ : Type
> NonNegQ = Subset Fraction Reduced


