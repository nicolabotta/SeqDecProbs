> module Rational

> import Data.Sign
> import Syntax.PreorderReasoning

> import SignProperties
> import NatPredicates


> %default total


> %hide sign


* Specification

> data Q : Type

> |||
> public fromIntegerQ : Integer -> Q

> |||
> public sign : Q -> Sign

> |||
> public numerator : Q -> Nat

> |||
> public denominator : Q -> Nat

> |||
> public denNotZero : (q : Q) -> Not (denominator q = Z)

> |||
> public numDenCoprime : (q : Q) -> Coprime (numerator q) (denominator q)

> |||
> public signZero : (q : Q) -> numerator q = Z -> sign q = Zero


* Predicates

> public NonNeg : Q -> Type
> NonNeg q = Not (sign q = Minus)

Patrik: TODO: Here (as in NonNegRational.lidr) it feels a bit
backwards to use |Not| when a positive formulation would be possible.

For example, with the natural ordering on Sign (TODO: define it - probably in Data.Sign in contrib).

NonNeg q = sign q > Minus


* Constants

** Zero

> public zeroQ : Q
> zeroQ = fromIntegerQ 0

> public zeroQLemma0 : sign zeroQ = Zero

> public nonNegZeroQ : NonNeg zeroQ
> nonNegZeroQ = s2 where
>   s1 : sign zeroQ = Zero
>   s1 = zeroQLemma0
>   s2 : Not (sign zeroQ = Minus)
>   s2 = replace {x = Zero} {y = sign zeroQ} {P = \ ZUZU => Not (ZUZU = Minus)} (sym s1) zeroNotMinus

** One

> public oneQ : Q
> oneQ = fromIntegerQ 1

> public oneQLemma0 : sign oneQ = Plus

> public nonNegOneQ : NonNeg oneQ
> nonNegOneQ = s2 where
>   s1 : sign oneQ = Plus
>   s1 = oneQLemma0
>   s2 : Not (sign oneQ = Minus)
>   s2 = replace {x = Plus} {y = sign oneQ} {P = \ ZUZU => Not (ZUZU = Minus)} (sym s1) plusNotMinus


* Operations

> |||
> public neg : Q -> Q

> public negSpec0 : (q : Q) -> sign q = Zero -> sign (neg q) = Zero
> public negSpec1 : (q : Q) -> sign q = Minus -> sign (neg q) = Plus
> public negSpec2 : (q : Q) -> sign q = Plus -> sign (neg q) = Minus

> |||
> public plus  : Q -> Q -> Q

> |||
> public minus : Q -> Q -> Q

> |||
> public mult  : Q -> Q -> Q


* Properties

> instance Num Q where
>   (+) = plus
>   (-) = minus
>   (*) = mult
>   
>   abs q = if (sign q == Minus) then neg q else q
>   
>   fromInteger = fromIntegerQ


> public plusSign1 : (q1 : Q) -> (q2 : Q) -> NonNeg q1 -> NonNeg q2 -> NonNeg (plus q1 q2)

> public plusSign1Spec : (q : Q) -> (nnq : NonNeg q) -> plusSign1 q zeroQ nnq nonNegZeroQ = nnq


> public multSign1 : (q1 : Q) -> (q2 : Q) -> NonNeg q1 -> NonNeg q2 -> NonNeg (mult q1 q2)


> public plusZeroLeftNeutral : (right : Q) -> zeroQ + right = right


> public plusZeroRightNeutral : (left : Q) -> left + zeroQ = left


This lemma

> public sumLemma0 : (q : Q) -> sum (q :: Nil) = q
> sumLemma0 q = ( plus q zeroQ )
>             ={ plusZeroRightNeutral q }=
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



> ---}


 
