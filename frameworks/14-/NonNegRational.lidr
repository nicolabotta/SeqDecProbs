> module NonNegRational

> import Data.Sign
> import Syntax.PreorderReasoning

> import Rational
> import NatPredicates
> import SignProperties
> import Basics



> %default total


* Specification

> ||| Non negative rationals
> data NonNegQ : Type where
>   MkNonNegQ : (q : Q) -> NonNeg q -> NonNegQ

Patrik: TODO: I have a feeling that using |Not| is overkill for finite
types like |Sign|. Note that the definition (|Not a = a -> Void|) uses
a function space so each element of |NonNegQ| will (at least
conceptually) contain a function.


* Basic operations and properties

> |||
> fromQ : (q : Q) -> Not (sign q = Minus) -> NonNegQ
> fromQ = MkNonNegQ

> |||
> toQ : NonNegQ -> Q
> toQ (MkNonNegQ q nnq) = q

> |||
> toQLemma : (q : NonNegQ) -> NonNeg (toQ q)
> toQLemma (MkNonNegQ q nnq) = nnq

> |||
> toQfromQLemma : (q : Q) -> (nnq : Not (sign q = Minus)) -> toQ (fromQ q nnq) = q
> toQfromQLemma q nnq = Refl

> |||
> fromIntegerNonNegQ : Integer -> NonNegQ
> fromIntegerNonNegQ i with (fromIntegerQ i)
>   | q with (decEq (sign q) Minus)
>       | Yes _ = fromQ zeroQ nonNegZeroQ
>       | No contra = fromQ q contra

> |||
> numerator : NonNegQ -> Nat
> numerator (MkNonNegQ q nnq) = numerator q

> |||
> denominator : NonNegQ -> Nat
> denominator (MkNonNegQ q nnq) = denominator q

> |||
> denNotZero : (q : NonNegQ) -> Not (denominator q = Z)
> denNotZero (MkNonNegQ q nnq) = denNotZero q

> |||
> numDenCoprime : (q : NonNegQ) -> Coprime (numerator q) (denominator q)
> numDenCoprime (MkNonNegQ q nnq) = numDenCoprime q


* Constants

> zeroNonNegQ : NonNegQ
> zeroNonNegQ = fromIntegerNonNegQ 0 

> zeroNonNegQLemma : zeroNonNegQ = fromQ zeroQ nonNegZeroQ

> oneNonNegQ : NonNegQ
> oneNonNegQ = fromIntegerNonNegQ 1 -- fromQ oneQ nonNegOneQ


* Operations

> plus : NonNegQ -> NonNegQ -> NonNegQ
> plus q1 q2 = fromQ q nnq where
>   q   : Q
>   q   = Rational.plus (toQ q1) (toQ q2)
>   nnq : NonNeg q
>   nnq = plusSign1 (toQ q1) (toQ q2) (toQLemma q1) (toQLemma q2)

> minus : NonNegQ -> NonNegQ -> NonNegQ
> minus q1 q2 with (Rational.minus (toQ q1) (toQ q2))
>   | q with (decEq (sign q) Minus)
>       | Yes _ = zeroNonNegQ
>       | No contra = fromQ q contra

> mult : NonNegQ -> NonNegQ -> NonNegQ
> mult q1 q2 = fromQ q nnq where
>   q   : Q
>   q   = Rational.mult (toQ q1) (toQ q2)
>   nnq : NonNeg q
>   nnq = multSign1 (toQ q1) (toQ q2) (toQLemma q1) (toQLemma q2)


* Properties

> instance Num NonNegQ where
>   (+) = plus
>   (-) = minus
>   (*) = mult
>   
>   abs q = q
>   
>   fromInteger = fromIntegerNonNegQ

> |||
> plusZeroRightNeutral : (left : NonNegQ) -> left + zeroNonNegQ = left
> plusZeroRightNeutral (MkNonNegQ q nnq) = 
>     ( MkNonNegQ q nnq + fromIntegerNonNegQ 0 )  
>   ={ replace {x = fromIntegerNonNegQ 0}
>              {y = fromQ zeroQ nonNegZeroQ}
>              {P = \ ZUZU => MkNonNegQ q nnq + fromIntegerNonNegQ 0 = MkNonNegQ q nnq + ZUZU}
>              zeroNonNegQLemma
>              Refl }=
>     ( MkNonNegQ q nnq + fromQ zeroQ nonNegZeroQ )  
>   ={ Refl }=
>     ( fromQ (Rational.plus q zeroQ) (plusSign1 q zeroQ nnq nonNegZeroQ) )
>   ={ depCong2 {alpha = Q}
>               {P = \ x => NonNeg x} 
>               {gamma = NonNegQ}
>               {a1 = Rational.plus q zeroQ}
>               {a2 = q}
>               {Pa1 = plusSign1 q zeroQ nnq nonNegZeroQ}
>               {Pa2 = nnq}
>               (\ x => \ nnx => fromQ x nnx)
>               (plusZeroRightNeutral q)
>               (plusSign1Spec q nnq) }=
>     ( fromQ q nnq )
>   ={ Refl }=
>     ( MkNonNegQ q nnq )
>   QED


This lemma

> sumLemma0 : (q : NonNegQ) -> sum (q :: Nil) = q
> sumLemma0 q = ( plus q zeroNonNegQ )          
>             ={ NonNegRational.plusZeroRightNeutral q }=
>               ( q )
>             QED

should be a consequence of |Q| being a monoid and of something like

< sumLemma1 : (Monoid alpha) => (a : alpha) -> sum (a :: Nil) = a
< sumLemma1 a = ( a + neutral )
<             ={ plusNeutralRightId }=
<               ( a )
<             QED

But due to #2489 we have to write ad-hoc implementations at the instance
level.

