> module FractionOperations


> import Fraction
> import PNat
> import PNatOperations
> import PNatProperties
> import NatGCD
> import NatGCDOperations
> import NatDivisor
> import NatDivisorOperations
> import NatDivisorProperties


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
> fromNat n = (n, Element (S Z) MkIsSucc)
> -- %freeze fromNat


> ||| Fraction addition
> plus : Fraction -> Fraction -> Fraction
> plus (n1, d1) (n2, d2) = (n1 * (toNat d2) + n2 * (toNat d1), d1 * d2)
> -- %freeze plus


> ||| Fraction multiplication
> mult : Fraction -> Fraction -> Fraction
> mult (n1, d1) (n2, d2) = (n1 * n2, d1 * d2)
> -- %freeze mult


> ||| Reduction to normal form (coprime numbers)
> reduce : ((m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>          Fraction -> Fraction
> reduce alg (m, n') =
>   let n     :  Nat
>             =  toNat n' in 
>   let dv    :  (d : Nat ** GCD d m n)
>             =  alg m n in
>   let d     :  Nat
>             =  getWitness dv in
>   let v     :  (GCD d m n)
>             =  getProof dv in 
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
