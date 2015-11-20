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


> ||| An equivalence relation (see below)
> Eq : Fraction -> Fraction -> Type
> Eq (m, d') (n, e') = let d = toNat d' in
>                      let e = toNat e' in
>                      m * e = n * d
> -- %freeze Eq

The idea is to use |Eq| implement non-negative rational numbers as
quotient of fractions by |Eq|. 

A naive approach toward implementing (non-negative) rational numbers
(for which equality is well represented by syntactical equality) could
be to define rational numbers as normalized fractions, something like

  NonNegRational = Subset Fraction Normal

where |Normal : Fraction -> Type| represents the property of being in
normal form, see "FractionNormal.lidr". It is easy to see that
|normalize| does indeed return fractions in normal form, see
|normalNormalize| in "FractionProperties.lidr". Thus, one could
implement addition and multiplication of rational numbers in terms of
|normalize| and of fraction addition and multiplication. For instance:

  plus : NonNegRational -> NonNegRational -> NonNegRational
  plus x' y' = let x   =  getWitness x' in
               let y   =  getWitness y' in
               Element (normalize (x + y)) (normalNormalize (x + y))

and similarly for multiplication. The problem with this approach is that
implementing proofs of

  1.  x + y = y + x
  2.  x + 0 = x
  3.  x + (y + z) = (x + y) + z
  4.  x * y = y * x
  5.  x * 1 = x

for fractions is tedious but trivial. Extending 1,2,4,5 to rational
numbers is pretty straightforward but extending 3 and deriving

  6.  x * (y + z) = (x * y) + (x * z)
  
(which does not hold for fractions) turns out to be a nightmare. With
|Eq| we can take advantage of Tim Richter's "SplitQuotient" and
"KernelQuotient" modules (see ...) to define ...

...

To this end, we only need to show that:

 a. Fraction addition and multiplication preserve Eq:

    a1.  (x Eq x') -> (y Eq y') -> (x + y) Eq (x' + y')   
    a2.  (x Eq x') -> (y Eq y') -> (x * y) Eq (x' * y')   

 b. Normalize fulfills: 

    b1.  (normalize x) Eq x
    b2.  x Eq y -> normalize x = normalize y

These properties are implemented via



< normalizeEqLemma1 : (x : Fraction) -> (normalize x) `Eq` x

< normalizeEqLemma2 : (x : Fraction) -> (y : Fraction) -> 
<                     x `Eq` y -> normalize x = normalize y
