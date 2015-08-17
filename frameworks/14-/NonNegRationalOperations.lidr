> module NonNegRationalOperations

> import Data.Sign

> import NonNegRational
> import RationalSpecification
> import RationalOperations
> import RationalProperties
> import SignedPredicates
> import SignProperties


> %default total


> |||
> numerator : NonNegQ -> Nat
> numerator (MkNonNegQ q nnq) = numerator q

> |||
> denominator : NonNegQ -> Nat
> denominator (MkNonNegQ q nnq) = denominator q

> |||
> fromIntegerNonNegQ : Integer -> NonNegQ
> fromIntegerNonNegQ i with (fromIntegerQ i)
>   | q with (decEq (sign q) Minus)
>       | Yes _ = fromQ zeroQ nonNegZeroQ
>       | No contra = fromQ q contra


Constants:

> zeroNonNegQ : NonNegQ
> zeroNonNegQ = fromIntegerNonNegQ 0

> oneNonNegQ : NonNegQ
> oneNonNegQ = fromIntegerNonNegQ 1 -- fromQ oneQ nonNegOneQ


Plus, minus, mult

> plus : NonNegQ -> NonNegQ -> NonNegQ
> plus q1 q2 = fromQ q nnq where
>   q   : Q
>   q   = RationalOperations.plus (toQ q1) (toQ q2)
>   nnq : NonNeg q
>   nnq = plusSign1 (toQ q1) (toQ q2) (toQLemma q1) (toQLemma q2)


> minus : NonNegQ -> NonNegQ -> NonNegQ
> minus q1 q2 with (RationalOperations.minus (toQ q1) (toQ q2))
>   | q with (decEq (sign q) Minus)
>       | Yes _ = zeroNonNegQ
>       | No contra = fromQ q contra


> mult : NonNegQ -> NonNegQ -> NonNegQ
> mult q1 q2 = fromQ q nnq where
>   q   : Q
>   q   = RationalOperations.mult (toQ q1) (toQ q2)
>   nnq : NonNeg q
>   nnq = multSign1 (toQ q1) (toQ q2) (toQLemma q1) (toQLemma q2)


