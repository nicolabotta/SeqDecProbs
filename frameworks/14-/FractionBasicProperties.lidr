> module FractionBasicProperties

> import Syntax.PreorderReasoning

> import Fraction
> import FractionBasicOperations
> import FractionNormal
> import NatLTProperties
> import PNat
> import PNatOperations
> import PNatProperties
> import NatPositive
> import Basics
> import NatCoprime
> import NatCoprimeProperties
> import NatOperationsProperties

> %default total
> %access public export


> ||| Denominators of fractions are greater than zero
> denLTLemma : (x : Fraction) -> Z `LT` den x
> denLTLemma x = s2 where
>   s1 : Z `LT` toNat (snd x)
>   s1 = toNatLTLemma (snd x)
>   s2 : Z `LT` den x
>   s2 = replace {P = \ ZUZU => Z `LT` ZUZU} Refl s1
> %freeze denLTLemma


> |||
> fromNatNormal : {n : Nat} -> Normal (fromNat n)
> fromNatNormal = MkNormal anyCoprimeOne
> %freeze fromNatNormal


> {-
> ||| Fraction is an instance of Show
> instance Show Fraction where
>   show q = show (num q) ++ "/" ++ show (den q)
> -}


> ||| Fraction is an instance of Num
> implementation Num Fraction where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat


Properties of |plus|:

> ||| Addition is commutative
> plusCommutative : (x : Fraction) -> (y : Fraction) -> x + y = y + x
> plusCommutative (m, d') (n, e') =
>   let d = toNat d' in
>   let e = toNat e' in
>     ( (m, d') + (n, e') )
>   ={ Refl }=
>     ( (m * e + n * d, d' * e') )
>   ={ cong2 (plusCommutative (m * e) (n * d)) (multCommutative d' e') }=
>     ( (n * d + m * e, e' * d') )
>   ={ Refl }=
>     ( (n, e') + (m, d') )
>   QED
> %freeze plusCommutative


> ||| 0 is neutral element of addition
> plusZeroRightNeutral : (x : Fraction) -> x + 0 = x
> plusZeroRightNeutral (n, d') =
>   let d = toNat d' in
>     ( (n, d') + 0 )
>   ={ Refl }=
>     ( (n, d') + fromNat (fromIntegerNat 0) )
>   ={ Refl }=
>     ( (n, d') + fromNat 0 )
>   ={ Refl }=
>     ( (n, d') + (0, Element 1 MkPositive) )
>   ={ Refl }=
>     ( (n * 1 + 0 * d, d' * (Element 1 MkPositive)) )
>   ={ cong2 (multOneRightNeutralPlusMultZeroLeftZero n d) (multOneRightNeutral d') }=
>     ( (n, d') )
>   QED
> %freeze plusZeroRightNeutral


> ||| 0 is neutral element of addition
> plusZeroLeftNeutral  : (x : Fraction) -> 0 + x = x
> plusZeroLeftNeutral x = 
>     ( 0 + x )
>   ={ plusCommutative 0 x }=
>     ( x + 0 )
>   ={ plusZeroRightNeutral x }=
>     ( x )
>   QED
> %freeze plusZeroLeftNeutral


> ||| Addition is associative
> plusAssociative : (x : Fraction) -> (y : Fraction) -> (z : Fraction) -> x + (y + z) = (x + y) + z
> plusAssociative (m, d') (n, e') (o, f') = 
>   let d = toNat d' in
>   let e = toNat e' in
>   let f = toNat f' in
>     ( (m, d') + ((n, e') + (o, f')) )
>   ={ Refl }=
>     ( (m, d') + (n * f + o * e, e' * f') )
>   ={ Refl }=
>     ( (m * (toNat (e' * f')) + (n * f + o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (m * (ZUZU) + (n * f + o * e) * d, d' * (e' * f'))} 
>           toNatMultLemma }=
>     ( (m * (e * f) + (n * f + o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (m * (e * f) + ZUZU, d' * (e' * f'))} 
>           (multDistributesOverPlusLeft (n * f) (o * e) d) }=
>     ( (m * (e * f) + ((n * f) * d + (o * e) * d), d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (ZUZU, d' * (e' * f'))}
>           (plusAssociative (m * (e * f)) ((n * f) * d) ((o * e) * d)) }=
>     ( ((m * (e * f) + (n * f) * d) + (o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => ((ZUZU + (n * f) * d) + (o * e) * d, d' * (e' * f'))}
>           (multAssociative m e f) }=
>     ( (((m * e) * f + (n * f) * d) + (o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (((m * e) * f + ZUZU) + (o * e) * d, d' * (e' * f'))}
>           (sym (multAssociative n f d)) }=
>     ( (((m * e) * f + n * (f * d)) + (o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (((m * e) * f + n * (ZUZU)) + (o * e) * d, d' * (e' * f'))}
>           (multCommutative f d) }=
>     ( (((m * e) * f + n * (d * f)) + (o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (((m * e) * f + ZUZU) + (o * e) * d, d' * (e' * f'))}
>           (multAssociative n d f) }=
>     ( (((m * e) * f + (n * d) * f) + (o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (ZUZU + (o * e) * d, d' * (e' * f'))}
>           (sym (multDistributesOverPlusLeft (m * e) (n * d) f)) }=
>     ( ((m * e + n * d) * f + (o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => ((m * e + n * d) * f + ZUZU, d' * (e' * f'))}
>           (sym (multAssociative o e d)) }=
>     ( ((m * e + n * d) * f + o * (e * d), d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => ((m * e + n * d) * f + o * (ZUZU), d' * (e' * f'))}
>           (multCommutative e d) }=  
>     ( ((m * e + n * d) * f + o * (d * e), d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => ((m * e + n * d) * f + o * (d * e), ZUZU)}
>           (multAssociative d' e' f')}=
>     ( ((m * e + n * d) * f + o * (d * e), (d' * e') * f') )
>   ={ cong {f = \ ZUZU => ((m * e + n * d) * f + o * (ZUZU), (d' * e') * f')}
>           (sym toNatMultLemma) }=
>     ( ((m * e + n * d) * f + o * (toNat (d' * e')), (d' * e') * f') )
>   ={ Refl }=  
>     ( (m * e + n * d, d' * e') + (o, f') )
>   ={ Refl }=
>     ( ((m, d') + (n, e')) + (o, f') )
>   QED
> %freeze plusAssociative


Properties of |mult|:

> ||| Multiplication is commutative
> multCommutative : (x : Fraction) -> (y : Fraction) -> x * y = y * x
> multCommutative (m, d') (n, e') =
>     ( (m, d') * (n, e') )
>   ={ Refl }=
>     ( (m * n, d' * e') )
>   ={ cong2 (multCommutative m n) (multCommutative d' e') }=
>     ( (n * m, e' * d') )
>   ={ Refl }=
>     ( (n, e') * (m, d') )
>   QED
> %freeze multCommutative


> ||| 1 is neutral element of multiplication
> multOneRightNeutral : (x : Fraction) -> x * 1 = x
> multOneRightNeutral (n, d') =
>   let d = toNat d' in
>     ( (n, d') * 1 )
>   ={ Refl }=
>     ( (n, d') * (fromNat (fromIntegerNat 1)) )
>   ={ Refl }=
>     ( (n, d') * (fromNat 1) )
>   ={ Refl }=
>     ( (n, d') * (1, Element 1 MkPositive) )
>   ={ Refl }=
>     ( (n * 1, d' * (Element 1 MkPositive)) )
>   ={ cong2 (multOneRightNeutral n) (multOneRightNeutral d') }=
>     ( (n, d') )
>   QED
> %freeze multOneRightNeutral


> ||| 1 is neutral element of multiplication
> multOneLeftNeutral  : (x : Fraction) -> 1 * x = x
> multOneLeftNeutral x = 
>     ( 1 * x )
>   ={ multCommutative 1 x }=
>     ( x * 1 )
>   ={ multOneRightNeutral x }=
>     ( x )
>   QED
> %freeze multOneLeftNeutral


> {-

> ---}

