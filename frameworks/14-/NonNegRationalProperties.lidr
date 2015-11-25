> module NonNegRationalProperties


> import Syntax.PreorderReasoning

> import NonNegRational
> import NonNegRationalOperations
> import Fraction
> import FractionOperations
> import FractionProperties
> import FractionNormal
> import SubsetProperties
> import Unique
> import NatPositive
> -- import PNat
> -- import NatCoprime
> 


> %default total


Properties of |toFraction|:

> |||
> toFractionEqLemma1 : {x, y : NonNegQ} -> (toFraction x) = (toFraction y) -> x = y
> toFractionEqLemma1 {x} {y} p = subsetEqLemma1 x y p NormalUnique 


> |||
> toFractionEqLemma2 : {x, y : NonNegQ} -> x = y -> (toFraction x) = (toFraction y)
> toFractionEqLemma2 {x} {y} p = getWitnessPreservesEq p 


Properties of |fromFraction| and |toFraction|:

> |||
> fromToId : (x : NonNegQ) -> fromFraction (toFraction x) = x
> fromToId (Element x nx) = ( fromFraction (toFraction (Element x nx)) )
>                         ={ Refl }=
>                           ( fromFraction x )
>                         ={ Refl }=
>                           ( Element (normalize x) (normalNormalize x) )
>                         ={ toFractionEqLemma1 (normalizePreservesNormal x nx) }=
>                           ( Element x nx )
>                         QED


> ||| NonNegQ is an instance of Show
> instance Show NonNegQ where
>   show q = show (num q) ++ "/" ++ show (den q)


> ||| NonNegQ is an instance of Num
> instance Num NonNegQ where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat


> |||
> toFractionFromIntegerLemma : (n : Integer) -> toFraction (fromInteger n) = fromInteger n



> ||| Addition is commutative
> plusCommutative : (x : NonNegQ) -> (y : NonNegQ) -> x + y = y + x
> plusCommutative x y =
>     ( x + y )
>   ={ Refl }=
>     ( fromFraction (toFraction x + toFraction y) )
>   ={ cong {f = fromFraction} (plusCommutative (toFraction x) (toFraction y)) }=
>     ( fromFraction (toFraction y + toFraction x) )
>   ={ Refl }=
>     ( y + x )
>   QED
> %freeze plusCommutative


> ||| 0 is neutral element of addition
> plusZeroRightNeutral : (x : NonNegQ) -> x + 0 = x
> plusZeroRightNeutral x =  
>     ( x + 0 )
>   ={ Refl }=
>     ( fromFraction (toFraction x + toFraction 0) )
>   ={ cong {f = fromFraction} (plusZeroRightNeutral (toFraction x)) }=
>     ( fromFraction (toFraction x) )
>   ={ fromToId x }=
>     ( x )
>   QED
> %freeze plusZeroRightNeutral


> ||| 0 is neutral element of addition
> plusZeroLeftNeutral : (x : NonNegQ) -> 0 + x = x
> plusZeroLeftNeutral x =   
>     ( 0 + x )
>   ={ plusCommutative 0 x }=
>     ( x + 0 )
>   ={ plusZeroRightNeutral x }=
>     ( x )
>   QED
> %freeze plusZeroLeftNeutral


> ||| Addition is associative
> plusAssociative : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) -> x + (y + z) = (x + y) + z
> plusAssociative x y z =
>   let x' = toFraction x in
>   let y' = toFraction y in
>   let z' = toFraction z in
>     ( x + (y + z) )
>   ={ Refl }=
>     ( fromFraction (x' + toFraction (fromFraction (y' + z'))) )
>   ={ Refl }=
>     ( fromFraction (x' + normalize (y' + z')) )
>   ={ Refl }=
>     ( Element (normalize (x' + normalize (y' + z'))) (normalNormalize (x' + normalize (y' + z'))) )
>   ={ toFractionEqLemma1 (normalizePlusElimRight x' (y' + z')) }=
>     ( Element (normalize (x' + (y' + z'))) (normalNormalize (x' + (y' + z'))) )
>   ={ toFractionEqLemma1 (cong (plusAssociative x' y' z')) }=
>     ( Element (normalize ((x' + y') + z')) (normalNormalize ((x' + y') + z')) )
>   ={ sym (toFractionEqLemma1 (normalizePlusElimLeft (x' + y') z')) }=
>     ( Element (normalize (normalize (x' + y') + z')) (normalNormalize (normalize (x' + y') + z')) )
>   ={ Refl }=  
>     ( fromFraction (normalize (x' + y') + z') )
>   ={ Refl }=
>     ( fromFraction (toFraction (fromFraction (x' + y')) + z') )
>   ={ Refl }=
>     ( (x + y) + z )
>   QED
> %freeze plusAssociative


> ||| Multiplication is commutative
> multCommutative : (x : NonNegQ) -> (y : NonNegQ) -> x * y = y * x
> multCommutative x y =
>     ( x * y )
>   ={ Refl }=
>     ( fromFraction ((toFraction x) * (toFraction y)) )
>   ={ cong {f = fromFraction} (multCommutative (toFraction x) (toFraction y)) }=
>     ( fromFraction ((toFraction y) * (toFraction x)) )
>   ={ Refl }=
>     ( y * x )
>   QED
> %freeze multCommutative


> ||| 1 is neutral element of multiplication
> multOneRightNeutral : (x : NonNegQ) -> x * 1 = x
> multOneRightNeutral x =  
>     ( x * 1 )
>   ={ Refl }=
>     ( fromFraction ((toFraction x) * (toFraction 1)) )
>   ={ Refl }=
>     ( fromFraction ((toFraction x) * (toFraction (fromInteger 1))) )
>   ={ cong {f = \ ZUZU => fromFraction ((toFraction x) * ZUZU)} (toFractionFromIntegerLemma 1) }=
>     ( fromFraction ((toFraction x) * (fromInteger 1)) )
>   ={ cong {f = fromFraction} (multOneRightNeutral (toFraction x)) }=
>     ( fromFraction (toFraction x) )
>   ={ fromToId x }=
>     ( x )
>   QED
> %freeze multOneRightNeutral


> ||| 1 is neutral element of multiplication
> multOneLeftNeutral : (x : NonNegQ) -> 1 * x = x
> multOneLeftNeutral x =   
>     ( 1 * x )
>   ={ multCommutative 1 x }=
>     ( x * 1 )
>   ={ multOneRightNeutral x }=
>     ( x )
>   QED
> %freeze multOneLeftNeutral


> {-
> |||
> multZeroPlusRightZero : (x : NonNegQ) -> x * 0 = 0
> multZeroPlusRightZero x =  
>     ( x * 0 )
>   ={ Refl }=
>     ( fromFraction ((toFraction x) * (toFraction 0)) )
>   ={ cong {f = fromFraction} (plusZeroRightNeutral (toFraction x)) }=
>     ( fromFraction (toFraction 0) )
>   ={ fromToId 0 }=
>     ( 0 )
>   QED
> %freeze multZeroPlusRightZero
> -}


> {-


> {- TODO: complete
> multZeroPlusRight : (x : NonNegQ) -> x * (fromInteger 0) = fromInteger 0
> multZeroPlusRight x@(MkNonNegQ n d zLTd gcdOne) =
>     (  x * (fromInteger 0)  )
>   ={ Refl }=
>     (  (MkNonNegQ n d zLTd gcdOne) * (MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z))  )
>   ={ Refl }=
>     (  fromFraction (n * Z) (d * (S Z)) (multZeroLTZeroLT d (S Z) zLTd (zeroLTden (fromInteger 0))))
>   ={ ?foo }=
>     (  fromInteger 0  )
>   QED
> -}

> {-

> multZeroPlusLeft  : (x : NonNegQ) -> (fromInteger 0) * x = fromInteger 0

> multOneRight      : (x : NonNegQ) -> x * (fromInteger 1) = x

> multOneLeft       : (x : NonNegQ) -> (fromInteger 1) * x = x


> multDistributesOverPlusRight : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) ->
>                                x * (y + z) = (x * y) + (x * z)

> multDistributesOverPlusLeft  : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) ->
>                                (x + y) * z = (x * z) + (y * z)

> -}

> ||| |fromInteger 1| is neutral element of multiplication
> multOneRightNeutral : (x : NonNegQ) -> x * (fromInteger 1) = x
> multOneRightNeutral x =  
>     ( x * (fromInteger 1) )
>   ={ Refl }=
>     ( reduce ((toFraction x) * (toFraction (fromInteger 1))) )
>   ={ cong (multOneRightNeutral (toFraction x)) }=
>     ( reduce (toFraction x) )
>   ={ reducePreservesReduced x }=
>     ( x )
>   QED
> %freeze multOneRightNeutral

> ---}
 
