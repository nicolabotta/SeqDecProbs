> module RationalProperties

> import Data.Sign
> import Syntax.PreorderReasoning

> import RationalSpecification
> import RationalOperations
> import SignedPredicates
> import SignProperties
> -- import NatPredicates
> -- import NatOperations
> -- import NatProperties


> %default total


Instances:

> instance Signed Q where
>   sign = sign


> instance Num Q where
>   (+) = plus
>   (-) = minus
>   (*) = mult
>   
>   abs q = if (sign q == Minus) then neg q else q
>   
>   fromInteger = fromIntegerQ


Properties of |zeroQ|:

> zeroQLemma0 : sign zeroQ = Zero

> nonNegZeroQ : NonNeg zeroQ
> nonNegZeroQ = s2 where
>   s1 : sign zeroQ = Zero
>   s1 = zeroQLemma0
>   s2 : Not (sign zeroQ = Minus)
>   s2 = replace {x = Zero} {y = sign zeroQ} {P = \ ZUZU => Not (ZUZU = Minus)} (sym s1) zeroNotMinus


Properties of |oneQ|:

> oneQLemma0 : sign oneQ = Plus

> nonNegOneQ : NonNeg oneQ
> nonNegOneQ = s2 where
>   s1 : sign oneQ = Plus
>   s1 = oneQLemma0
>   s2 : Not (sign oneQ = Minus)
>   s2 = replace {x = Plus} {y = sign oneQ} {P = \ ZUZU => Not (ZUZU = Minus)} (sym s1) plusNotMinus


> plusSign1 : (q1 : Q) -> (q2 : Q) -> NonNeg q1 -> NonNeg q2 -> NonNeg (plus q1 q2)

> plusSign1Spec : (q : Q) -> (nnq : NonNeg q) -> plusSign1 q zeroQ nnq nonNegZeroQ = nnq


> multSign1 : (q1 : Q) -> (q2 : Q) -> NonNeg q1 -> NonNeg q2 -> NonNeg (mult q1 q2)


> plusZeroLeftNeutral : (right : Q) -> zeroQ + right = right


> plusZeroRightNeutral : (left : Q) -> left + zeroQ = left


This lemma

> sumLemma0 : (q : Q) -> sum (q :: Nil) = q
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



 
