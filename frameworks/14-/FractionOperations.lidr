> module FractionOperations


> import Fraction
> import PNat
> import PNatOperations
> import PNatProperties
> import NatPositive
> import NatGCD
> import NatGCDOperations
> import NatDivisor
> import NatDivisorOperations
> import NatDivisorProperties
> import NatGCDAlgorithm


> %default total


> ||| The numerator of a fraction
> num : Fraction -> Nat
> num = fst
> -- %freeze num


> ||| The denominator of a fraction
> den : Fraction -> Nat
> den = toNat . snd
> -- %freeze den


> ||| Every natural number is a fraction
> fromNat : Nat -> Fraction
> fromNat n = (n, Element (S Z) MkPositive)
> -- %freeze fromNat


> ||| Fraction addition
> plus : Fraction -> Fraction -> Fraction
> plus (n1, d1) (n2, d2) = (n1 * (toNat d2) + n2 * (toNat d1), d1 * d2)
> -- %freeze plus


> ||| Fraction multiplication
> mult : Fraction -> Fraction -> Fraction
> mult (n1, d1) (n2, d2) = (n1 * n2, d1 * d2)
> -- %freeze mult


> ||| Fraction upscaling
> upscale : Fraction -> PNat -> Fraction
> upscale (m, d) e = (m * (toNat e), d * e)
> -- %freeze upscale


> ||| Reduction to normal form
> normalize : Fraction -> Fraction
> normalize (m, d') =
>   let d       :  Nat
>               =  toNat d' in 
>   let g       :  Nat
>               =  gcdAlg m d in
>   let prf     :  (GCD g m d)
>               =  gcdAlgLemma m d in 
>   let gDm     :  (g `Divisor` m)
>               =  gcdDivisorFst prf in
>   let gDd     :  (g `Divisor` d)
>               =  gcdDivisorSnd prf in
>   let qmg     :  Nat
>               =  quotient m g gDm in
>   let qdg     :  Nat
>               =  quotient d g gDd in
>   let zLTd    :  (Z `LT` d)
>               =  toNatLTLemma d' in 
>   let zLTqdg  :  (Z `LT` qdg) 
>               =  quotientPreservesPositivity d g gDd zLTd in
>   (qmg, fromNat qdg zLTqdg)
> -- %freeze normalize


> ||| An equivalence relation Eq: the idea is that Eq will be used to define
> ||| non-negative rational numbers as quotient of fractions by Eq. For
> ||| this, we have to implement a
> |||  
> |||   normalize : Fraction -> Fraction
> |||
> ||| and show that 
> |||
> |||   x `Eq` normalize x
> |||
> |||   x `Eq` y => normalize x = normalize y
> |||
> ||| and that addition and multiplication preserve Eq. 
> Eq : Fraction -> Fraction -> Type
> Eq (m, d') (n, e') = let d = toNat d' in
>                      let e = toNat e' in
>                      m * e = n * d
> -- %freeze Eq


> {-

> ---}
