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
>             ={ ?lala }=
>               ( num (fromNatNonNegQ Z) )
>             ={ Refl }=
>               -- ( num (MkNonNegQ Z (S Z) SIsNotZ anyCoprimeOne) )
>               ( num (MkNonNegQ Z (S Z) (ltZS Z) anyCoprimeOne) )
>             ={ Refl }=
>               ( Z )
>             QED

> denZeroOne : den (fromInteger 0) = S Z


Properties of casts:

> fromFractionLemma : (n : Nat) -> (d : Nat) -> 
>                     (ndCoprime : Coprime n d) -> (zLTd : Z `LT` d) -> 
>                     fromFraction n d zLTd = MkNonNegQ n d zLTd ndCoprime
> fromFractionLemma n d ndCoprime zLTd with (decCoprime n d)
>   | (Yes prf) = ( MkNonNegQ n d zLTd prf )
>               ={ replace {x = prf}
>                          {y = ndCoprime} 
>                          {P = \ ZUZU => MkNonNegQ n d zLTd prf = MkNonNegQ n d zLTd ZUZU} 
>                          (uniqueCoprime n d prf ndCoprime) Refl}=
>                 ( MkNonNegQ n d zLTd ndCoprime )
>               QED
>   | (No contra) = void (contra ndCoprime)


In order to implement simple probability distributions based on
non-negative rational numbers, we need these to fulfill

> plusZeroPlusRight : (x : NonNegQ) -> x + (fromInteger 0) = x
> plusZeroPlusRight x = s11 where
>   s01 : x + (fromInteger 0) = x + MkNonNegQ Z (S Z) (ltZS Z) anyCoprimeOne
>   s01 = Refl
>   s02 : x + MkNonNegQ Z (S Z) (ltZS Z) anyCoprimeOne 
>         =
>         fromFraction ((num x) * (S Z) + Z * (den x)) 
>                      ((den x) * (S Z)) 
>                      (multZeroLTZeroLT (den x) (S Z) (zeroLTden x) (ltZS Z))
>   s02 = Refl   
>   s03 : fromFraction ((num x) * (S Z) + Z * (den x)) 
>                      ((den x) * (S Z)) 
>                      (multZeroLTZeroLT (den x) (S Z) (zeroLTden x) (ltZS Z))
>         =
>         fromFraction (num x) 
>                      (den x)
>                      (multZeroLTZeroLT (den x) (S Z) (zeroLTden x) (ltZS Z))
>   s03 = ?juju
>   s04 : fromFraction (num x) 
>                      (den x) 
>                      (multZeroLTZeroLT (den x) (S Z) (zeroLTden x) (ltZS Z))
>         =
>         MkNonNegQ (num x) (den x) (multZeroLTZeroLT (den x) (S Z) (zeroLTden x) (ltZS Z)) (numDenCoprime x)
>   s04 = fromFractionLemma (num x) (den x) (numDenCoprime x)
>   s04 : MkNonNegQ (num x) (den x) (multZeroLTZeroLT (den x) (S Z) (zeroLTden x) (ltZS Z)) (numDenCoprime x)
>         =
>         x
>   s04 = ?kiki      
>   s11 : x + (fromInteger 0) = x
>   s11 = trans s01 (trans s02 (trans s03 (trans s04)))

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
