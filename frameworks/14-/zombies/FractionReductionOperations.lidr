> module FractionReduction


> import Fraction
> import FractionOperations
> import FractionReduction
> import PNat
> import PNatOperations
> import PNatProperties
> import NatGCD
> import NatGCDOperations
> import NatGCDProperties
> import NatDivisor
> import NatDivisorOperations
> import NatDivisorProperties
> import NatGCDAlgorithm
> import NatCoprime
> import NatCoprimeProperties


> %default total

> {-

> ||| Reduction to normal form
> reduce : Fraction -> Fraction
> reduce (m, n') =
>   let n     :  Nat
>             =  toNat n' in 
>   let d     :  Nat
>             =  gcdAlg m n in
>   let v     :  (GCD d m n)
>             =  gcdAlgLemma m n in 
>   let dDm   :  (d `Divisor` m)
>             =  gcdDivisorFst v in
>   let dDn   :  (d `Divisor` n)
>             =  gcdDivisorSnd v in
>   let o     :  Nat
>             =  quotient m d dDm in
>   let p     :  Nat
>             =  quotient n d dDn in
>   let zLTn  :  (Z `LT` n)
>             =  toNatLTLemma n' in 
>   let zLTp  :  (Z `LT` p) 
>             =  quotientPreservesPositivity n d dDn zLTn in
>    
>   (o, fromNat p zLTp)
> -- %freeze reduce

> -}
 
> --{-
 
> ||| Reduction to normal form
> reduce : Fraction -> Subset Fraction Reduced
> reduce (m, n') =
>   let n       :  Nat
>               =  toNat n' in 
>   let d       :  Nat
>               =  gcdAlg m n in
>   let dGCDmn  :  (GCD d m n)
>               =  gcdAlgLemma m n in 
>   let dDm     :  (d `Divisor` m)
>               =  gcdDivisorFst dGCDmn in
>   let dDn     :  (d `Divisor` n)
>               =  gcdDivisorSnd dGCDmn in
>   let o       :  Nat
>               =  quotient m d dDm in
>   let p       :  Nat
>               =  quotient n d dDn in
>   let zLTn    :  (Z `LT` n)
>               =  toNatLTLemma n' in 
>   let zLTp    :  (Z `LT` p) 
>               =  quotientPreservesPositivity n d dDn zLTn in
>   let zLTd    :  (Z `LT` d)
>               =  gcdPreservesPositivity2 zLTn (d ** dGCDmn) in
>    
>   Element (o, fromNat p zLTp) (MkReduced (gcdCoprimeLemma d m n dDm dDn zLTd dGCDmn))
> -- %freeze reduce

> ---}
