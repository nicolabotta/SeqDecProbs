> module FractionNormalize

> import Fraction
> import FractionBasicOperations
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
> %access public export


> ||| Reduction to normal form via gcdAlg (NatGCDAlgorithm)
> normalize : Fraction -> Fraction
> normalize (m, d') = (qmg, fromNat qdg zLTqdg) where
>   d       :  Nat
>   d       =  toNat d'
>   g       :  Nat
>   g       =  gcdAlg m d
>   prf     :  (GCD g m d)
>   prf     =  gcdAlgLemma m d
>   gDm     :  (g `Divisor` m)
>   gDm     =  gcdDivisorFst prf
>   gDd     :  (g `Divisor` d)
>   gDd     =  gcdDivisorSnd prf
>   qmg     :  Nat
>   qmg     =  quotient m g gDm
>   qdg     :  Nat
>   qdg     =  quotient d g gDd
>   zLTd    :  (Z `LT` d)
>   zLTd    =  toNatLTLemma d'
>   zLTqdg  :  (Z `LT` qdg) 
>   zLTqdg  =  quotientPreservesPositivity d g gDd zLTd
> -- %freeze normalize


> {-
> ||| Reduction to normal form via gcdAlg (NatGCDAlgorithm)
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
> ---}


