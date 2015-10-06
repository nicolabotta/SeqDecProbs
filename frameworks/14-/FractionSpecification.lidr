> module FractionSpecification


> %default total


> ||| A type representing a fraction
> Fraction : Type
  
  
> ||| The numerator of a fraction
> num : Fraction -> Nat
  
  
> ||| The denominator of a fraction
> den : Fraction -> Nat
  
  
> ||| Every natural number is a fraction
> fromNat : Nat -> Fraction
  
  
> ||| Fraction addition
> plus : Fraction -> Fraction -> Fraction
  
> ||| Addition preserves positivity of denominators
> plusPreservesPositivity : (x : Fraction) -> (y : Fraction) -> 
>                           Z `LT` den x -> Z `LT` den y -> 
>                           Z `LT` den (x `plus` y)
  
> ||| Addition is commutative
> plusCommutative : (x : Fraction) -> (y : Fraction) -> 
>                   x `plus` y = y `plus` x

> ||| Addition is associative
> plusAssociative : (x : Fraction) -> (y : Fraction) -> (z : Fraction) -> 
>                   x `plus` (y `plus` z) = (x `plus` y) `plus` z
  
  
> ||| Fraction multiplication
> mult : Fraction -> Fraction -> Fraction

> ||| Multiplication preserves positivity of denominators
> multPreservesPositivity : (x : Fraction) -> (y : Fraction) -> 
>                           Z `LT` den x -> Z `LT` den y -> 
>                           Z `LT` den (x `mult` y)

> ||| Multiplication is commutative
> multCommutative : (x : Fraction) -> (y : Fraction) -> 
>                   x `mult` y = y `mult` x

> ||| Multiplication is associative
> multAssociative : (x : Fraction) -> (y : Fraction) -> (z : Fraction) -> 
>                   x `mult` (y `mult` z) = (x `mult` y) `mult` z


This is a limited example: a full specification would possibly require
distributivity properties, neutral elements, etc.

The interesting question here is "what is a minimal set of requirements
that allows one to derive interesting properties of fractions
independently of their actual implementation (representation)?", see
also FractionImplementationIndependentProperties.lidr

For instance, what is a minimal set of requirementes that allows one to
say that |Fraction| is an instance of |Num|? Or of |Ring|?


