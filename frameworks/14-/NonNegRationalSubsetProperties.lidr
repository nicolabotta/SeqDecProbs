> module NonNegRationalSubsetProperties

> import Data.Sign
> import Syntax.PreorderReasoning

> import NonNegRationalSubset
> import NonNegRationalSubsetOperations
> import RationalSpecification
> import RationalOperations
> import RationalProperties
> import NatPredicates
> import SignedPredicates
> import SignProperties
> import Basics
> import NumRefinements


> %default total


> ||| Non-negative rationals are in |Num|
> instance Num NonNegQ where
>   (+) = plus
>   (-) = minus
>   (*) = mult
>
>   abs q = q
>
>   fromInteger = fromIntegerNonNegQ


Properties of numerator, denominator:

> |||
> denNotZero : (q : NonNegQ) -> Not (denominator q = Z)
> denNotZero (MkNonNegQ q nnq) = denNotZero q

> |||
> numDenCoprime : (q : NonNegQ) -> Coprime (numerator q) (denominator q)
> numDenCoprime (MkNonNegQ q nnq) = numDenCoprime q


Properties of |zeroNonNegQ|:

> zeroNonNegQLemma : zeroNonNegQ = fromQ zeroQ nonNegZeroQ


Properties of |plus|:

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
>     ( fromQ (RationalOperations.plus q zeroQ) (plusSign1 q zeroQ nnq nonNegZeroQ) )
>   ={ depCong2 {alpha = Q}
>               {P = \ x => NonNeg x}
>               {gamma = NonNegQ}
>               {a1 = RationalOperations.plus q zeroQ}
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


...

> ||| Non-negative rationals are in ||
> instance NumMultDistributesOverPlus NonNegQ where






This lemma

> sumLemma0 : (q : NonNegQ) -> sum (q :: Nil) = q
> sumLemma0 q = ( plus q zeroNonNegQ )
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
