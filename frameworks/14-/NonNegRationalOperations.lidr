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
> -- denNotZero : (q : NonNegQ) -> Not (den q = Z)
> -- denNotZero (MkNonNegQ _ _ dNotZ _) = dNotZ

> |||
> zeroLTden : (q : NonNegQ) -> Z `LT` (den q)
> zeroLTden (MkNonNegQ _ _ zLTd _) = zLTd

> |||
> numDenCoprime : (q : NonNegQ) -> Coprime (num q) (den q)
> numDenCoprime (MkNonNegQ _ _ _ ndCoprime) = ndCoprime


Casts:

> |||
> fromNatNonNegQ : (n : Nat) -> NonNegQ
> -- fromNatNonNegQ n = MkNonNegQ n (S Z) SIsNotZ anyCoprimeOne
> fromNatNonNegQ n = MkNonNegQ n (S Z) (ltZS Z) anyCoprimeOne

> |||
> fromIntegerNonNegQ : Integer -> NonNegQ
> fromIntegerNonNegQ = fromNatNonNegQ . fromIntegerNat

> {-

> ||| Computes a non-negative rational number from a fraction
> fromFraction : (n' : Nat) -> (d' : Nat) -> Not (d' = Z) -> NonNegQ
> fromFraction n' d' d'NotZ = MkNonNegQ n d dNotZ ndCoprime where
>   gcdv : (gcd : Nat ** GCD gcd n' d')
>   gcdv = euclidGCD n' d'
>   gcd : Nat
>   gcd = getWitness gcdv
>   v : GCD gcd n' d'
>   v = getProof gcdv
>   n : Nat
>   n = divBy gcd n' (gcdDivisorFst v)
>   d : Nat
>   d = divBy gcd d' (gcdDivisorSnd v)
>   gcddNotZ : Not (gcd * d = Z)
>   gcddNotZ = replace {x = d'} 
>                      {y = gcd * d} 
>                      {P = \ ZUZU => Not (ZUZU = Z)} 
>                      (sym (divByLemma gcd d' (gcdDivisorSnd v))) d'NotZ
>   gcdNotZ : Not (gcd = Z)
>   gcdNotZ = multNotZeroNotZeroLeft gcd d gcddNotZ 
>   dNotZ : Not (d = Z)
>   dNotZ = multNotZeroNotZeroRight gcd d gcddNotZ 
>   ndCoprime : Coprime n d
>   ndCoprime = gcdCoprimeLemma' v gcdNotZ

> -}

> ||| Computes a non-negative rational number from a fraction
> fromFraction : (n' : Nat) -> (d' : Nat) -> Z `LT` d' -> NonNegQ
> {-
> fromFraction n' d' zLTd' = MkNonNegQ n d zLTd ndCoprime where
>   gcdv : (gcd : Nat ** GCD gcd n' d')
>   gcdv = euclidGCD n' d'
>   gcd : Nat
>   gcd = getWitness gcdv
>   v : GCD gcd n' d'
>   v = getProof gcdv
>   n : Nat
>   n = divBy gcd n' (gcdDivisorFst v)
>   d : Nat
>   d = divBy gcd d' (gcdDivisorSnd v)
>   zLTgcdd : Z `LT` gcd * d
>   zLTgcdd = replace {x = d'} 
>                     {y = gcd * d} 
>                     {P = \ ZUZU => Z `LT` ZUZU} 
>                     (sym (divByLemma gcd d' (gcdDivisorSnd v))) zLTd'
>   zLTgcd : Z `LT` gcd
>   zLTgcd = multLTZeroLeftLTZero gcd d zLTgcdd 
>   zLTd : Z `LT` d
>   zLTd = multLTZeroRightLTZero gcd d zLTgcdd 
>   ndCoprime : Coprime n d
>   ndCoprime = gcdCoprimeLemma'' v zLTgcd
> -}
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


Constants:

> zeroNonNegQ : NonNegQ
> zeroNonNegQ = fromIntegerNonNegQ 0

> oneNonNegQ : NonNegQ
> oneNonNegQ = fromIntegerNonNegQ 1


|plus|, |mult|, ...

> plus : NonNegQ -> NonNegQ -> NonNegQ
> -- plus q1 q2 = fromFraction n' d' d'NotZ where
> plus q1 q2 = fromFraction n' d' zLTd' where
>   n' : Nat
>   n' = (num q1) * (den q2) + (num q2) * (den q1)
>   d' : Nat
>   d' = (den q1) * (den q2)
>   -- d'NotZ : Not (d' = Z)
>   -- d'NotZ = multNotZeroNotZero (den q1) (den q2) (denNotZero q1) (denNotZero q2)
>   zLTd' : Z `LT` d'
>   zLTd' = multZeroLTZeroLT (den q1) (den q2) (zeroLTden q1) (zeroLTden q2)

> mult : NonNegQ -> NonNegQ -> NonNegQ
> -- mult q1 q2 = fromFraction n' d' d'NotZ where
> mult q1 q2 = fromFraction n' d' zLTd' where
>   n' : Nat
>   n' = (num q1) * (num q2)
>   d' : Nat
>   d' = (den q1) * (den q2)
>   -- d'NotZ : Not (d' = Z)
>   -- d'NotZ = multNotZeroNotZero (den q1) (den q2) (denNotZero q1) (denNotZero q2)
>   zLTd' : Z `LT` d'
>   zLTd' = multZeroLTZeroLT (den q1) (den q2) (zeroLTden q1) (zeroLTden q2)

> minus : NonNegQ -> NonNegQ -> NonNegQ
> -- minus q1 q2 = fromFraction n' d' d'NotZ where
> minus q1 q2 = fromFraction n' d' zLTd' where
>   n' : Nat
>   n' = (num q1) * (den q2) - (num q2) * (den q1)
>   d' : Nat
>   d' = (den q1) * (den q2)
>   -- d'NotZ : Not (d' = Z)
>   -- d'NotZ = multNotZeroNotZero (den q1) (den q2) (denNotZero q1) (denNotZero q2)
>   zLTd' : Z `LT` d'
>   zLTd' = multZeroLTZeroLT (den q1) (den q2) (zeroLTden q1) (zeroLTden q2)

> {-

> ---}




