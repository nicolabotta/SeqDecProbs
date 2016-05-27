> module NonNegRationalProperties


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
> import FractionLTEProperties
> import FractionNormal
> import SubsetProperties
> import Unique
> import NatPositive
> import NumRefinements
> import PairsOperations
> import NatLTEProperties
> import NatOperationsProperties
> import ListProperties 
 

> %default total

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


> ||| Denominators of non-negative rationals are greater than zero
> denLTLemma : (x : NonNegRational) -> Z `LT` den x
> denLTLemma x = s2 where
>   s1 : Z `LT` den (toFraction x)
>   s1 = FractionBasicProperties.denLTLemma (toFraction x)
>   s2 : Z `LT` den x
>   s2 = replace {P = \ ZUZU => Z `LT` ZUZU} Refl s1


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
>   plusZeroLeftNeutral = NonNegRationalProperties.plusZeroLeftNeutral
>   plusZeroRightNeutral = NonNegRationalProperties.plusZeroRightNeutral


> ||| NonNegRational is an implementation of NumPlusAssociative
> implementation NumPlusAssociative NonNegRational where
>   plusAssociative = NonNegRationalProperties.plusAssociative


> ||| NonNegRational is an implementation of NumMultZeroOne
> implementation NumMultZeroOne NonNegRational where
>   multZeroRightZero   = NonNegRationalProperties.multZeroRightZero
>   multZeroLeftZero    = NonNegRationalProperties.multZeroLeftZero
>   multOneRightNeutral = NonNegRationalProperties.multOneRightNeutral
>   multOneLeftNeutral  = NonNegRationalProperties.multOneLeftNeutral


> ||| NonNegRational is an implementation NumMultDistributesOverPlus
> implementation NumMultDistributesOverPlus NonNegRational where
>   multDistributesOverPlusRight = NonNegRationalProperties.multDistributesOverPlusRight
>   multDistributesOverPlusLeft  = NonNegRationalProperties.multDistributesOverPlusLeft


Properties of |LTE|:

> ||| LTE is reflexive
> reflexiveLTE : (x : NonNegRational) -> x `LTE` x
> reflexiveLTE x = reflexiveLTE (toFraction x)
> %freeze reflexiveLTE


> ||| LTE is transitive
> transitiveLTE : (x, y, z : NonNegRational) -> x `LTE` y -> y `LTE` z -> x `LTE` z
> transitiveLTE x y z xLTEy yLTEz = transitiveLTE (toFraction x) (toFraction y) (toFraction z) xLTEy yLTEz
> %freeze transitiveLTE


> ||| LTE is total
> totalLTE : (x, y : NonNegRational) -> Either (x `LTE` y) (y `LTE` x) 
> totalLTE x y = totalLTE (toFraction x) (toFraction y)
> %freeze totalLTE


> ||| LTE is monotone w.r.t. `plus`
> monotonePlusLTE : {a, b, c, d : NonNegRational} -> 
>                   a `LTE` b -> c `LTE` d -> (a + c) `LTE` (b + d)
> monotonePlusLTE {a} {b} {c} {d} aLTEb cLTEd = s4 where
>   s1 : LTE (toFraction a + toFraction c) (toFraction b + toFraction d)
>   s1 = FractionLTEProperties.monotonePlusLTE aLTEb cLTEd
>   s2 : LTE (normalize (toFraction a + toFraction c)) 
>            (normalize (toFraction b + toFraction d))
>   s2 = normalizeLTELemma (toFraction a + toFraction c) (toFraction b + toFraction d) s1
>   s3 : LTE (toFraction (fromFraction (toFraction a + toFraction c)))
>            (toFraction (fromFraction (toFraction b + toFraction d)))
>   s3 = s2
>   s4 : LTE (fromFraction (toFraction a + toFraction c)) (fromFraction (toFraction b + toFraction d))
>   s4 = s3
>   s5 : LTE (a + c) (b + d)
>   s5 = s4
> %freeze monotonePlusLTE


> ||| LTE is monotone w.r.t. `(*)`
> monotoneMultLTE : {a, b, c, d : NonNegRational} -> 
>                   a `LTE` b -> c `LTE` d -> (a * c) `LTE` (b * d)
> monotoneMultLTE {a} {b} {c} {d} aLTEb cLTEd = s4 where
>   s1 : LTE (toFraction a * toFraction c) (toFraction b * toFraction d)
>   s1 = FractionLTEProperties.monotoneMultLTE aLTEb cLTEd
>   s2 : LTE (normalize (toFraction a * toFraction c)) 
>            (normalize (toFraction b * toFraction d))
>   s2 = normalizeLTELemma (toFraction a * toFraction c) (toFraction b * toFraction d) s1
>   s3 : LTE (toFraction (fromFraction (toFraction a * toFraction c)))
>            (toFraction (fromFraction (toFraction b * toFraction d)))
>   s3 = s2
>   s4 : LTE (fromFraction (toFraction a * toFraction c)) (fromFraction (toFraction b * toFraction d))
>   s4 = s3
>   s5 : LTE (a * c) (b * d)
>   s5 = s4
> %freeze monotoneMultLTE


Properties of |sum|, |average|:

> ||| |sum| is monotone
> monotoneSum : {A : Type} ->
>               (f : A -> NonNegRational) -> (g : A -> NonNegRational) ->
>               (p : (a : A) -> f a `LTE` g a) ->
>               (as : List A) ->
>               sum (map f as) `LTE` sum (map g as) 
> monotoneSum f g p Nil = LTEZero
> monotoneSum f g p (a :: as) = s5 where
>   s1 : sum (map f (a :: as)) = f a + sum (map f as)
>   s1 = Refl
>   s2 : sum (map g (a :: as)) = g a + sum (map g as)
>   s2 = Refl
>   s3 : f a `LTE` g a
>   s3 = p a
>   s4 : sum (map f as) `LTE` sum (map g as)
>   s4 = monotoneSum f g p as
>   s5 : sum (map f (a :: as)) `LTE` sum (map g (a :: as))
>   s5 = NonNegRationalProperties.monotonePlusLTE s3 s4
> %freeze monotoneSum


> factor : {A : Type} -> List A -> NonNegRational
> factor Nil = 1
> factor (a :: as) = fromFraction (1, Element (S (length as)) MkPositive)


> factorLemma : {A, B, C : Type} -> 
>               (as : List A) -> (f : A -> B) -> (g : A -> C) ->
>               factor (map f as) = factor (map g as)
> factorLemma  Nil f g = Refl
> factorLemma (a :: as) f g = 
>     ( factor (map f (a :: as)) )
>   ={ Refl }=
>     ( factor (f a :: map f as) )
>   ={ Refl }=
>     ( fromFraction (1, Element (S (length (map f as))) MkPositive) )
>   ={ cong {f = \ ZUZU => fromFraction (1, Element (S ZUZU) MkPositive)} (lengthLemma as f g) }=
>     ( fromFraction (1, Element (S (length (map g as))) MkPositive) )  
>   ={ Refl }=
>     ( factor (g a :: map g as) )
>   ={ Refl }=
>     ( factor (map g (a :: as)) )
>   QED
> %freeze factorLemma


> ||| 
> average : List NonNegRational -> NonNegRational
> average xs = (sum xs) * (factor xs)


> ||| |average| is monotone
> monotoneAverage : {A : Type} ->
>                   (f : A -> NonNegRational) -> (g : A -> NonNegRational) ->
>                   (p : (a : A) -> f a `LTE` g a) ->
>                   (as : List A) ->
>                   average (map f as) `LTE` average (map g as) 
> monotoneAverage f g p as = monotoneMultLTE {a = sum (map f as)} 
>                                            {b = sum (map g as)} 
>                                            {c = factor (map f as)} 
>                                            {d = factor (map g as)}
>                                            s1 s3 where
>   s1 : sum (map f as) `LTE` sum (map g as)
>   s1 = monotoneSum f g p as
>   s2 : factor (map f as) `LTE` factor (map f as)
>   s2 = reflexiveLTE (factor (map f as))
>   s3 : factor (map f as) `LTE` factor (map g as)
>   s3 = replace {P = \ ZUZU => factor (map f as) `LTE` ZUZU} (factorLemma as f g) s2


> {-

> ---}
 
