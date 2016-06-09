> module NonNegRationalBasicProperties


> import Syntax.PreorderReasoning

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalPredicates
> import Fraction
> import FractionBasicOperations
> import FractionPredicates
> import FractionBasicProperties
> import FractionNormalize
> import FractionNormalizeProperties
> import FractionEqProperties
> import FractionNormal
> import SubsetProperties
> import Unique
> import UniqueProperties
> import NatPositive
> import NumRefinements
> import PairsOperations
> import NatLTEProperties
> import NatOperationsProperties
> import ListProperties 
> import PNat
> import PNatOperations
> import PNatProperties 
> import Basics

> %default total

> -- %access export
> %access public export


Properties of |toFraction|:

> ||| toFraction is injective
> toFractionInjective : {x, y : NonNegRational} -> (toFraction x) = (toFraction y) -> x = y
> toFractionInjective {x} {y} p = subsetEqLemma1 x y p NormalUnique 
> %freeze toFractionInjective


> ||| toFraction preserves equality
> toFractionEqLemma2 : {x, y : NonNegRational} -> x = y -> (toFraction x) = (toFraction y)
> toFractionEqLemma2 {x} {y} p = getWitnessPreservesEq p 
> %freeze toFractionEqLemma2


Properties of |fromFraction| and |toFraction|:

> ||| fromFraction is left inverse of toFraction
> fromToId : (x : NonNegRational) -> fromFraction (toFraction x) = x
> fromToId (Element x nx) = ( fromFraction (toFraction (Element x nx)) )
>                         ={ Refl }=
>                           ( fromFraction x )
>                         ={ Refl }=
>                           ( Element (normalize x) (normalNormalize x) )
>                         ={ toFractionInjective (normalizePreservesNormal x nx) }=
>                           ( Element x nx )
>                         QED
> %freeze fromToId


> ||| Equivalence of fractions implies equality of non-negative rationals 
> fromFractionEqLemma : (x, y : Fraction) -> x `Eq` y -> fromFraction x = fromFraction y
> fromFractionEqLemma x y xEqy = s7 where
>   s1 : normalize x = normalize y
>   s1 = normalizeEqLemma2 x y xEqy
>   s2 : Normal (normalize x) = Normal (normalize y)
>   s2 = cong s1
>   s3 : Normal (normalize x)
>   s3 = normalNormalize x
>   s4 : Normal (normalize y)
>   s4 = normalNormalize y
>   s5 : s3 = s4
>   s5 = uniqueLemma (\ f => NormalUnique {x = f}) (normalize x) (normalize y) s3 s4 s1
>   s6 : Element (normalize x) (normalNormalize x) = Element (normalize y) (normalNormalize y)
>   s6 = depCong2 {alpha = Fraction} 
>                 {P = Normal} 
>                 {gamma = Subset Fraction Normal}
>                 {a1 = normalize x} 
>                 {a2 = normalize y}
>                 {Pa1 = normalNormalize x} 
>                 {Pa2 = normalNormalize y} 
>                 {f = \ ZUZU => \ ZAZA => Element ZUZU ZAZA} s1 s5 
>   s7 : fromFraction x = fromFraction y
>   s7 = s6
> %freeze fromFractionEqLemma


> ||| Denominators of non-negative rationals are greater than zero
> denLTLemma : (x : NonNegRational) -> Z `LT` den x
> denLTLemma x = s2 where
>   s1 : Z `LT` den (toFraction x)
>   s1 = FractionBasicProperties.denLTLemma (toFraction x)
>   s2 : Z `LT` den x
>   s2 = replace {P = \ ZUZU => Z `LT` ZUZU} Refl s1
> %freeze denLTLemma


> ||| 
> toFractionFromNatLemma : (n : Nat) -> toFraction (fromNat n) = fromNat n
> toFractionFromNatLemma n =
>     ( toFraction (fromNat n) )
>   ={ Refl }=
>     ( toFraction (fromFraction (fromNat n)) )
>   ={ Refl }=
>     ( toFraction (fromFraction (n, Element (S Z) MkPositive)) )
>   ={ Refl }=
>     ( toFraction (Element (normalize (n, Element (S Z) MkPositive)) (normalNormalize (n, Element (S Z) MkPositive))) )
>   ={ cong (toFractionInjective (normalizePreservesNormal (n, Element (S Z) MkPositive) fromNatNormal)) }=
>     ( toFraction (Element (n, Element (S Z) MkPositive) fromNatNormal) )
>   ={ Refl }=
>     ( (n, Element (S Z) MkPositive) )
>   ={ Refl }=
>     ( fromNat n )
>   QED
> %freeze toFractionFromNatLemma


> ||| NonNegRational is an implementation of Show
> implementation Show NonNegRational where
>   show q = show (num q) ++ "/" ++ show (den q)


> ||| NonNegRational is an implementation of Num
> implementation Num NonNegRational where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat


> |||
> toFractionFromIntegerLemma : (n : Integer) -> toFraction (fromInteger n) = fromInteger n
> toFractionFromIntegerLemma n =
>     ( toFraction (fromInteger n) )
>   ={ Refl }=
>     ( toFraction (fromNat (fromIntegerNat n)) )
>   ={ toFractionFromNatLemma (fromIntegerNat n) }=
>     ( fromNat (fromIntegerNat n) )
>   ={ Refl }=
>     ( fromInteger n )
>   QED
> %freeze toFractionFromIntegerLemma


> ||| Addition is commutative
> plusCommutative : (x : NonNegRational) -> (y : NonNegRational) -> x + y = y + x
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
> plusZeroRightNeutral : (x : NonNegRational) -> x + 0 = x
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
> plusZeroLeftNeutral : (x : NonNegRational) -> 0 + x = x
> plusZeroLeftNeutral x =   
>     ( 0 + x )
>   ={ plusCommutative 0 x }=
>     ( x + 0 )
>   ={ plusZeroRightNeutral x }=
>     ( x )
>   QED
> %freeze plusZeroLeftNeutral


> ||| Addition is associative
> plusAssociative : (x, y, z : NonNegRational) -> x + (y + z) = (x + y) + z
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
>   ={ toFractionInjective (normalizePlusElimRight x' (y' + z')) }=
>     ( Element (normalize (x' + (y' + z'))) (normalNormalize (x' + (y' + z'))) )
>   ={ toFractionInjective (cong (plusAssociative x' y' z')) }=
>     ( Element (normalize ((x' + y') + z')) (normalNormalize ((x' + y') + z')) )
>   ={ sym (toFractionInjective (normalizePlusElimLeft (x' + y') z')) }=
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
> multCommutative : (x : NonNegRational) -> (y : NonNegRational) -> x * y = y * x
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
> multOneRightNeutral : (x : NonNegRational) -> x * 1 = x
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
> multOneLeftNeutral : (x : NonNegRational) -> 1 * x = x
> multOneLeftNeutral x =   
>     ( 1 * x )
>   ={ multCommutative 1 x }=
>     ( x * 1 )
>   ={ multOneRightNeutral x }=
>     ( x )
>   QED
> %freeze multOneLeftNeutral


> |||
> multZeroRightZero : (x : NonNegRational) -> x * 0 = 0
> multZeroRightZero x = 
>   let x' = toFraction x in 
>     ( x * 0 )
>   ={ Refl }=
>     ( fromFraction (x' * 0) )
>   ={ Refl }=
>     ( Element (normalize (x' * 0)) (normalNormalize (x' * 0)) )
>   ={ toFractionInjective (normalizeEqLemma2 (x' * 0) 0 (multZeroRightEqZero x')) }=
>     ( Element (normalize 0) (normalNormalize 0) )
>   ={ Refl }=
>     ( fromFraction 0 )
>   ={ fromToId 0 }=
>     ( 0 )
>   QED
> %freeze multZeroRightZero


> ||| 
> multZeroLeftZero : (x : NonNegRational) -> 0 * x = 0
> multZeroLeftZero x =   
>     ( 0 * x )
>   ={ multCommutative 0 x }=
>     ( x * 0 )
>   ={ multZeroRightZero x }=
>     ( 0 )
>   QED
> %freeze multZeroLeftZero


> |||
> multDistributesOverPlusRight : (x, y, z : NonNegRational) -> x * (y + z) = (x * y) + (x * z)
> multDistributesOverPlusRight x y z =
>   let x' = toFraction x in
>   let y' = toFraction y in
>   let z' = toFraction z in
>     ( x * (y + z) )
>   ={ Refl }=
>     ( fromFraction (x' * toFraction (fromFraction (y' + z'))) )
>   ={ Refl }=
>     ( fromFraction (x' * (normalize (y' + z'))) )
>   ={ Refl }=
>     ( Element (normalize (x' * (normalize (y' + z')))) (normalNormalize (x' * (normalize (y' + z')))) )
>   ={ toFractionInjective (normalizeMultElimRight x' (y' + z')) }=
>     ( Element (normalize (x' * (y' + z'))) (normalNormalize (x' * (y' + z'))) )
>   ={ toFractionInjective (normalizeEqLemma2 (x' * (y' + z')) ((x' * y') + (x' * z')) multDistributesOverPlusRightEq) }=
>     ( Element (normalize ((x' * y') + (x' * z'))) (normalNormalize ((x' * y') + (x' * z'))) )
>   ={ toFractionInjective (sym (normalizePlusElim (x' * y') (x' * z'))) }=
>     ( Element (normalize (normalize (x' * y') + normalize (x' * z'))) 
>               (normalNormalize (normalize (x' * y') + normalize (x' * z'))) )
>   ={ Refl }=
>     ( fromFraction ((normalize (x' * y')) + (normalize (x' * z'))) )
>   ={ Refl }=
>     ( fromFraction ((toFraction (fromFraction (x' * y'))) + (toFraction (fromFraction (x' * z')))) )
>   ={ Refl }=
>     ( (x * y) + (x * z) )
>   QED
> %freeze multDistributesOverPlusRight


> |||
> multDistributesOverPlusLeft  : (x, y, z : NonNegRational) -> (x + y) * z = (x * z) + (y * z)
> multDistributesOverPlusLeft x y z =
>     ( (x + y) * z )
>   ={ multCommutative (x + y) z }=
>     ( z * (x + y) )
>   ={ multDistributesOverPlusRight z x y }=
>     ( z * x + z * y )
>   ={ cong {f = \ ZUZU => ZUZU + z * y} (multCommutative z x) }=
>     ( x * z + z * y )
>   ={ cong {f = \ ZUZU => x * z + ZUZU} (multCommutative z y) }=
>     ( x * z + y * z ) 
>   QED  
> %freeze multDistributesOverPlusLeft


> ||| NonNegRational is an implementation of NumPlusZeroNeutral
> implementation NumPlusZeroNeutral NonNegRational where
>   plusZeroLeftNeutral = NonNegRationalBasicProperties.plusZeroLeftNeutral
>   plusZeroRightNeutral = NonNegRationalBasicProperties.plusZeroRightNeutral


> ||| NonNegRational is an implementation of NumPlusAssociative
> implementation NumPlusAssociative NonNegRational where
>   plusAssociative = NonNegRationalBasicProperties.plusAssociative


> ||| NonNegRational is an implementation of NumMultZeroOne
> implementation NumMultZeroOne NonNegRational where
>   multZeroRightZero   = NonNegRationalBasicProperties.multZeroRightZero
>   multZeroLeftZero    = NonNegRationalBasicProperties.multZeroLeftZero
>   multOneRightNeutral = NonNegRationalBasicProperties.multOneRightNeutral
>   multOneLeftNeutral  = NonNegRationalBasicProperties.multOneLeftNeutral


> ||| NonNegRational is an implementation NumMultDistributesOverPlus
> implementation NumMultDistributesOverPlus NonNegRational where
>   multDistributesOverPlusRight = NonNegRationalBasicProperties.multDistributesOverPlusRight
>   multDistributesOverPlusLeft  = NonNegRationalBasicProperties.multDistributesOverPlusLeft


> {-

> ---}
 
