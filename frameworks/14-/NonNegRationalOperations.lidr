> module NonNegRationalOperations


> import NonNegRational
> import NatGCD
> import NatGCDOperations
> import NatGCDEuclid
> import Fraction
> import NatProperties
> import NatCoprime
> import NatCoprimeProperties


> %default total


Projections:

> ||| The numerator of a non-negative rational
> num : NonNegQ -> Nat
> num (MkNonNegQ n _ _ _) = n

> ||| The denominator of a non-negative rational
> den : NonNegQ -> Nat
> den (MkNonNegQ _ d _ _) = d

> ||| The denominator of a non-negative rational is not zero
> zeroLTden : (q : NonNegQ) -> Z `LT` (den q)
> zeroLTden (MkNonNegQ _ _ zLTd _) = zLTd

> ||| Numerator and denominator of non-negative rationals are coprime
> numDenCoprime : (q : NonNegQ) -> gcd (alg (num q) (den q)) = S Z
> numDenCoprime (MkNonNegQ _ _ _ gcdOne) = gcdOne


Casts:

> ||| Every natural number is a non-negative rational
> fromNat : (n : Nat) -> NonNegQ
> fromNat n = MkNonNegQ n (S Z) (ltZS Z) (gcdAnyOneOne alg n)


> ||| Every non-negative rational is a fraction
> toFraction : NonNegQ -> Fraction
> toFraction (MkNonNegQ n d _ _) = (n, d)


> toFractionPreservesNumerator : (q : NonNegQ) -> num (toFraction q) = num q
> toFractionPreservesNumerator (MkNonNegQ n d _ _) = Refl 


> toFractionPreservesDenominator : (q : NonNegQ) -> den (toFraction q) = den q
> toFractionPreservesDenominator (MkNonNegQ n d _ _) = Refl 


> toFractionPreservesDenominatorPositivity : (q : NonNegQ) -> Z `LT` den (toFraction q)
> toFractionPreservesDenominatorPositivity q = 
>   replace {x = den q} 
>           {y = Fraction.den (toFraction q)}
>           {P = \ ZUZU => Z `LT` ZUZU}
>           (sym (toFractionPreservesDenominator q)) (zeroLTden q)


> ||| Computes a non-negative rational number from a fraction
> fromFraction : (x : Fraction) -> Z `LT` den x -> NonNegQ
> fromFraction x zLTden = MkNonNegQ n d zLTd ndCoprime where
>   y : Fraction
>   y = reduce alg x 
>   n : Nat
>   n = num y
>   d : Nat
>   d = den y
>   zLTd : Z `LT` d
>   zLTd = reducePreservesPositivity alg x zLTden
>   ndCoprime : gcd (alg n d) = S Z
>   ndCoprime = gcdOneCoprimeLemma2 n d alg (reduceYieldsCoprimes alg x zLTden)


Constants:

> zeroNonNegQ : NonNegQ
> zeroNonNegQ = fromNat (fromInteger 0)

> oneNonNegQ : NonNegQ
> oneNonNegQ = fromNat (fromInteger 1)


|plus|, |mult|, ...

> plus : NonNegQ -> NonNegQ -> NonNegQ
> plus q1 q2 = fromFraction x p where
>   x1 : Fraction
>   x1 = toFraction q1
>   x2 : Fraction
>   x2 = toFraction q2
>   p1 : Z `LT` den x1
>   p1 = toFractionPreservesDenominatorPositivity q1
>   p2 : Z `LT` den x2
>   p2 = toFractionPreservesDenominatorPositivity q2
>   x  : Fraction
>   x  = x1 + x2
>   p  : Z `LT` den x
>   p  = plusPreservesPositivity x1 x2 p1 p2

> mult : NonNegQ -> NonNegQ -> NonNegQ
> mult q1 q2 = fromFraction x p where
>   x1 : Fraction
>   x1 = toFraction q1
>   x2 : Fraction
>   x2 = toFraction q2
>   p1 : Z `LT` den x1
>   p1 = toFractionPreservesDenominatorPositivity q1
>   p2 : Z `LT` den x2
>   p2 = toFractionPreservesDenominatorPositivity q2
>   x  : Fraction
>   x  = x1 * x2
>   p  : Z `LT` den x
>   p  = multPreservesPositivity x1 x2 p1 p2

> {-

> ---}
