> module NonNegRational


> import Fraction
> import FractionNormal


> %default total
> %access public export


> ||| Non negative rational numbers
> NonNegRational : Type
> NonNegRational = Subset Fraction Normal


