> module NonNegRationalProperties

> import Syntax.PreorderReasoning

> import NonNegRational
> import NonNegRationalOperations
> import NatPredicates
> import NatOperations
> import NatProperties
> import Basics
> import NumRefinements
> import GCD
> import EqualityProperties


> %default total


> ||| Non-negative rationals are in |Show|
> instance Show NonNegQ where
>   show q = show (num q) ++ "/" ++ show (den q)


> ||| Non-negative rationals are in |Num|
> instance Num NonNegQ where
>   (+) = plus
>   (-) = minus
>   (*) = mult
>   abs q = q
>   fromInteger = fromIntegerNonNegQ


Properties of |num|, |den|:

> numZeroZero : num (fromInteger 0) = Z
> numZeroZero = ( num (fromInteger 0) )
>             ={ Refl }=
>               ( num (fromNatNonNegQ (fromIntegerNat 0)) )
>             ={ Refl }=
>               ( num (fromNatNonNegQ Z) )
>             ={ Refl }=
>               ( num (MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z)) )
>             ={ Refl }=
>               ( Z )
>             QED

> -- denZeroOne : den (fromInteger 0) = S Z


Properties of casts:

> fromFractionLemma1 : (n : Nat) -> (d : Nat) ->  
>                      (zLTd : Z `LT` d) -> (gcdOne : gcd (alg n d) = S Z) ->
>                      fromFraction n d zLTd = MkNonNegQ n d zLTd gcdOne
> fromFractionLemma1 n d zLTd gcdOne with (decEq (gcd (alg n d)) (S Z))
>   | (Yes prf)   = ( MkNonNegQ n d zLTd prf )
>                 ={ replace {x = prf}
>                            {y = gcdOne}
>                            {P = \ ZUZU => MkNonNegQ n d zLTd prf = MkNonNegQ n d zLTd ZUZU}
>                            (uniqueEq (gcd (alg n d)) (S Z) prf gcdOne) 
>                            Refl }=
>                   ( MkNonNegQ n d zLTd gcdOne )
>                 QED  
>   | (No contra) = void (contra gcdOne)

> fromFractionLemma2 : (n : Nat) -> (d : Nat) -> (zLTd : Z `LT` d) ->
>                      (n' : Nat) -> (d' : Nat) -> (zLTd' : Z `LT` d') ->  
>                      n = n' -> d = d' ->
>                      fromFraction n d zLTd = fromFraction n' d' zLTd'
> fromFractionLemma2 n d zLTd n' d' zLTd' nEQn' dEQd' = trans s2 s3 where
>   s1 : zLTd = zLTd'
>   s1 = uniqueLT' Refl dEQd' zLTd zLTd'
>   s2 : fromFraction n d zLTd = fromFraction n' d zLTd
>   s2 = replace {x = n}
>                {y = n'}
>                {P = \ ZUZU => fromFraction n d zLTd = fromFraction ZUZU d zLTd}
>                nEQn' Refl
>   s3 : fromFraction n' d zLTd = fromFraction n' d' zLTd'
>   s3 = depCong2' {alpha = Nat}
>                  {P = \ ZUZU => Z `LT` ZUZU}
>                  {Q = \ ZUZU => \ zLTZUZU => NonNegQ}
>                  {a1 = d}
>                  {a2 = d'}
>                  {Pa1 = zLTd}
>                  {Pa2 = zLTd'} 
>                  (\ ZUZU => \ zLTZUZU => fromFraction n' ZUZU zLTZUZU) 
>                  dEQd' s1

In order to implement simple probability distributions based on
non-negative rational numbers, we need these to fulfill

> plusZeroPlusRight : (x : NonNegQ) -> x + (fromInteger 0) = x
> plusZeroPlusRight (MkNonNegQ n d zLTd gcdOne) = s7 where
>   s1 : (MkNonNegQ n d zLTd gcdOne) + (fromInteger 0) 
>        = 
>        (MkNonNegQ n d zLTd gcdOne) + MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z)
>   s1 = Refl
>   s2 : (MkNonNegQ n d zLTd gcdOne) + MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z)
>        =
>        fromFraction (n * (S Z) + Z * d) 
>                     (d * (S Z)) 
>                     (multZeroLTZeroLT d (S Z) zLTd (ltZS Z))
>   s2 = Refl
>   s3 : n * (S Z) + Z * d = n
>   s3 = ( n * (S Z) + Z * d )
>      ={ replace {x = n * (S Z)} 
>                 {y = n} 
>                 {P = \ ZUZU => n * (S Z) + Z * d = ZUZU + Z * d} 
>                 (multOneRightNeutral n) Refl}=
>        ( n + Z * d )
>      ={ replace {x = Z * d} 
>                 {y = Z}
>                 {P = \ ZUZU => n + Z * d = n + ZUZU}
>                 (multZeroLeftZero d) Refl }=
>        ( n + Z )
>      ={ plusZeroRightNeutral n }=
>        ( n )
>      QED    
>   s4 : d * (S Z) = d
>   s4 = multOneRightNeutral d
>   s5 : fromFraction (n * (S Z) + Z * d) 
>                     (d * (S Z)) 
>                     (multZeroLTZeroLT d (S Z) zLTd (ltZS Z))
>        =
>        fromFraction n d zLTd     
>   s5 = fromFractionLemma2 (n * (S Z) + Z * d) (d * (S Z)) (multZeroLTZeroLT d (S Z) zLTd (ltZS Z))
>                           n d zLTd s3 s4 
>   s6 : fromFraction n d zLTd = MkNonNegQ n d zLTd gcdOne
>   s6 = fromFractionLemma1 n d zLTd gcdOne
>   s7 : (MkNonNegQ n d zLTd gcdOne) + (fromInteger 0) = (MkNonNegQ n d zLTd gcdOne)
>   s7 = trans s1 (trans s2 (trans s5 s6))

> {-

> plusZeroPlusLeft  : (x : NonNegQ) -> (fromInteger 0) + x = x


> plusAssoc : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) -> x + (y + z) = (x + y) + z


> multZeroPlusRight : (x : NonNegQ) -> x * (fromInteger 0) = fromInteger 0

> multZeroPlusLeft  : (x : NonNegQ) -> (fromInteger 0) * x = fromInteger 0

> multOneRight      : (x : NonNegQ) -> x * (fromInteger 1) = x

> multOneLeft       : (x : NonNegQ) -> (fromInteger 1) * x = x


> multDistributesOverPlusRight : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) ->
>                                x * (y + z) = (x * y) + (x * z)
                                  
> multDistributesOverPlusLeft  : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) ->
>                                (x + y) * z = (x * z) + (y * z)

> ---}
 
