> module NonNegRationalOperations


> import NonNegRational
> import NatPredicates
> import NatOperations
> import NatProperties
> import GCD


> %default total


Projections:

> |||
> num : NonNegQ -> Nat
> num (MkNonNegQ n _ _ _) = n

> |||
> den : NonNegQ -> Nat
> den (MkNonNegQ _ d _ _) = d

> |||
> zeroLTden : (q : NonNegQ) -> Z `LT` (den q)
> zeroLTden (MkNonNegQ _ _ zLTd _) = zLTd

> |||
> numDenCoprime : (q : NonNegQ) -> gcd (alg (num q) (den q)) = S Z
> numDenCoprime (MkNonNegQ _ _ _ gcdOne) = gcdOne


Casts:

> |||
> fromNatNonNegQ : (n : Nat) -> NonNegQ
> -- fromNatNonNegQ n = MkNonNegQ n (S Z) (ltZS Z) anyCoprimeOne
> fromNatNonNegQ n = MkNonNegQ n (S Z) (ltZS Z) (gcdAnyOneOne alg n)

> |||
> fromIntegerNonNegQ : Integer -> NonNegQ
> fromIntegerNonNegQ = fromNatNonNegQ . fromIntegerNat

> ||| Computes a non-negative rational number from a fraction
> fromFraction : (n' : Nat) -> (d' : Nat) -> Z `LT` d' -> NonNegQ
> fromFraction n' d' zLTd' with (decEq (gcd (alg n' d')) (S Z))
>   | (Yes prf) = MkNonNegQ n' d' zLTd' prf
>   | (No    _) = MkNonNegQ n d zLTd gcdndOne where
>       gcdv' : (gcd' : Nat ** GCD gcd' n' d')
>       gcdv' = alg n' d'
>       gcd' : Nat
>       gcd' = getWitness gcdv'
>       v' : GCD gcd' n' d'
>       v' = getProof gcdv'
>       n : Nat
>       n = divBy gcd' n' (gcdDivisorFst v')
>       d : Nat
>       d = divBy gcd' d' (gcdDivisorSnd v')
>       zLTgcdd : Z `LT` gcd' * d
>       zLTgcdd = replace {x = d'} 
>                         {y = gcd' * d} 
>                         {P = \ ZUZU => Z `LT` ZUZU} 
>                         (sym (divByLemma gcd' d' (gcdDivisorSnd v'))) zLTd'
>       zLTgcd : Z `LT` gcd'
>       zLTgcd = multLTZeroLeftLTZero gcd' d zLTgcdd 
>       zLTd : Z `LT` d
>       zLTd = multLTZeroRightLTZero gcd' d zLTgcdd 
>       ndCoprime : Coprime n d
>       ndCoprime = gcdCoprimeLemma'' v' zLTgcd
>       gcdndOne : gcd (alg n d) = S Z
>       gcdndOne = gcdOneCoprimeLemma2 n d alg ndCoprime
>   
> {-
> fromFraction n' d' zLTd' with (decCoprime n' d')
>   | (Yes prf) = MkNonNegQ n' d' zLTd' prf
>   | (No  _  ) = MkNonNegQ n d zLTd ndCoprime where
>       gcdv : (gcd : Nat ** GCD gcd n' d')
>       gcdv = euclidGCD n' d'
>       gcd : Nat
>       gcd = getWitness gcdv
>       v : GCD gcd n' d'
>       v = getProof gcdv
>       n : Nat
>       n = divBy gcd n' (gcdDivisorFst v)
>       d : Nat
>       d = divBy gcd d' (gcdDivisorSnd v)
>       zLTgcdd : Z `LT` gcd * d
>       zLTgcdd = replace {x = d'} 
>                         {y = gcd * d} 
>                         {P = \ ZUZU => Z `LT` ZUZU} 
>                         (sym (divByLemma gcd d' (gcdDivisorSnd v))) zLTd'
>       zLTgcd : Z `LT` gcd
>       zLTgcd = multLTZeroLeftLTZero gcd d zLTgcdd 
>       zLTd : Z `LT` d
>       zLTd = multLTZeroRightLTZero gcd d zLTgcdd 
>       ndCoprime : Coprime n d
>       ndCoprime = gcdCoprimeLemma'' v zLTgcd
> -}


Constants:

> zeroNonNegQ : NonNegQ
> zeroNonNegQ = fromIntegerNonNegQ 0

> oneNonNegQ : NonNegQ
> oneNonNegQ = fromIntegerNonNegQ 1


|plus|, |mult|, ...

> plus : NonNegQ -> NonNegQ -> NonNegQ
> plus q1 q2 = fromFraction n' d' zLTd' where
>   n' : Nat
>   n' = (num q1) * (den q2) + (num q2) * (den q1)
>   d' : Nat
>   d' = (den q1) * (den q2)
>   zLTd' : Z `LT` d'
>   zLTd' = multZeroLTZeroLT (den q1) (den q2) (zeroLTden q1) (zeroLTden q2)

> mult : NonNegQ -> NonNegQ -> NonNegQ
> mult q1 q2 = fromFraction n' d' zLTd' where
>   n' : Nat
>   n' = (num q1) * (num q2)
>   d' : Nat
>   d' = (den q1) * (den q2)
>   zLTd' : Z `LT` d'
>   zLTd' = multZeroLTZeroLT (den q1) (den q2) (zeroLTden q1) (zeroLTden q2)

> minus : NonNegQ -> NonNegQ -> NonNegQ
> minus q1 q2 = fromFraction n' d' zLTd' where
>   n' : Nat
>   n' = (num q1) * (den q2) - (num q2) * (den q1)
>   d' : Nat
>   d' = (den q1) * (den q2)
>   zLTd' : Z `LT` d'
>   zLTd' = multZeroLTZeroLT (den q1) (den q2) (zeroLTden q1) (zeroLTden q2)

> {-

> ---}




