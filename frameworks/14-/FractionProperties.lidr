> module FractionProperties

> import Syntax.PreorderReasoning

> import Fraction
> import FractionOperations
> import PNat


> %default total


> ||| Fraction is an instance of Num
> instance Num Fraction where
>   (+) = plus
>   (*) = mult
>   fromInteger = FractionOperations.fromNat . fromIntegerNat

> {-


> ||| Addition is commutative
> plusCommutative : (x : Fraction) -> (y : Fraction) -> x + y = y + x
> plusCommutative (n1, d1) (n2, d2) = 
>     ( (n1, d1) + (n2, d2) )
>   ={ Refl }=
>     ( (n1 * d2 + n2 * d1, d1 * d2) )
>   ={ replace {x = n1 * d2 + n2 * d1}
>              {y = n2 * d1 + n1 * d2}
>              {P = \ ZUZU => (n1 * d2 + n2 * d1, d1 * d2) = (ZUZU, d1 * d2)}
>              (Nat.plusCommutative (n1 * d2) (n2 * d1)) Refl }=
>     ( (n2 * d1 + n1 * d2, d1 * d2) )
>   ={ replace {x = d1 * d2}
>              {y = d2 * d1}
>              {P = \ ZUZU => (n2 * d1 + n1 * d2, d1 * d2) = (n2 * d1 + n1 * d2, ZUZU)}
>              (Nat.multCommutative d1 d2) Refl }=           
>     ( (n2 * d1 + n1 * d2, d2 * d1) )
>   ={ Refl }=
>     ( (n2, d2) + (n1, d1) )
>   QED
> %freeze plusCommutative


> ||| |fromInteger 0| is neutral element of addition
> plusZeroPlusRight : (x : Fraction) -> x + (fromInteger 0) = x
> plusZeroPlusRight (n, d) =
>     ( (n, d) + (fromInteger 0) )
>   ={ Refl }=
>     ( (n, d) + (Z, S Z) )
>   ={ Refl }=
>     ( (n * (S Z) + Z * d, d * (S Z)) )
>   ={ replace {x = n * (S Z)}
>              {y = n}
>              {P = \ ZUZU => (n * (S Z) + Z * d, d * (S Z)) = (ZUZU + Z * d, d * (S Z))}
>              (multOneRightNeutral n) Refl }=
>     ( (n + Z * d, d * (S Z)) )
>   ={ Refl }=
>     ( (n + Z, d * (S Z)) )
>   ={ replace {x = n + Z}
>              {y = n}
>              {P = \ ZUZU => (n + Z, d * (S Z)) = (ZUZU, d * (S Z))}
>              (plusZeroRightNeutral n) Refl }=
>     ( (n, d * (S Z)) )
>   ={ replace {x = d * (S Z)}
>              {y = d}
>              {P = \ ZUZU => (n, d * (S Z)) = (n, ZUZU)}
>              (multOneRightNeutral d) Refl }=
>     ( (n, d) )
>   QED
> %freeze plusZeroPlusRight


> ||| |fromInteger 0| is neutral element of addition
> plusZeroPlusLeft  : (x : Fraction) -> (fromInteger 0) + x = x
> plusZeroPlusLeft x = 
>     ( (fromInteger 0) + x )
>   ={ plusCommutative (fromInteger 0) x }=
>     ( x + (fromInteger 0) )
>   ={ plusZeroPlusRight x }=
>     ( x )
>   QED
> %freeze plusZeroPlusLeft


> ||| Addition is associative
> plusAssociative : (x : Fraction) -> (y : Fraction) -> (z : Fraction) -> x + (y + z) = (x + y) + z
> plusAssociative (n1, d1) (n2, d2) (n3, d3) =
>     ( (n1, d1) + ((n2, d2) + (n3, d3)) )
>   ={ Refl }=
>     ( (n1, d1) + (n2 * d3 + n3 * d2, d2 * d3) )
>   ={ Refl }=
>     ( (n1 * (d2 * d3) + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3)) )
>   ={ replace {x = n1 * (d2 * d3)}
>              {y = (n1 * d2) * d3}
>              {P = \ ZUZU => (n1 * (d2 * d3) + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3))
>                             =
>                             (ZUZU + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3))}
>              (multAssociative n1 d2 d3) Refl }=
>     ( ((n1 * d2) * d3 + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3)) )
>   ={ replace {x = (n2 * d3 + n3 * d2) * d1}
>              {y = (n2 * d3) * d1 + (n3 * d2) * d1}
>              {P = \ ZUZU => ((n1 * d2) * d3 + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3))
>                             =
>                             ((n1 * d2) * d3 + (ZUZU), d1 * (d2 * d3))}
>              (multDistributesOverPlusLeft (n2 * d3) (n3 * d2) d1) Refl }=
>     ( ((n1 * d2) * d3 + ((n2 * d3) * d1 + (n3 * d2) * d1), d1 * (d2 * d3)) )
>   ={ replace {x = (n2 * d3) * d1}
>              {y = n2 * (d3 * d1)}
>              {P = \ ZUZU => ((n1 * d2) * d3 + ((n2 * d3) * d1 + (n3 * d2) * d1), d1 * (d2 * d3))
>                             =
>                             ((n1 * d2) * d3 + (ZUZU + (n3 * d2) * d1), d1 * (d2 * d3))}
>              (sym (multAssociative n2 d3 d1)) Refl }=
>     ( ((n1 * d2) * d3 + (n2 * (d3 * d1) + (n3 * d2) * d1), d1 * (d2 * d3)) )
>   ={ replace {x = d3 * d1}
>              {y = d1 * d3}
>              {P = \ ZUZU => ((n1 * d2) * d3 + (n2 * (d3 * d1) + (n3 * d2) * d1), d1 * (d2 * d3))
>                             =
>                             ((n1 * d2) * d3 + (n2 * (ZUZU) + (n3 * d2) * d1), d1 * (d2 * d3))}
>              (multCommutative d3 d1) Refl }=
>     ( ((n1 * d2) * d3 + (n2 * (d1 * d3) + (n3 * d2) * d1), d1 * (d2 * d3)) )
>   ={ replace {x = n2 * (d1 * d3)}
>              {y = (n2 * d1) * d3}
>              {P = \ ZUZU => ((n1 * d2) * d3 + (n2 * (d1 * d3) + (n3 * d2) * d1), d1 * (d2 * d3))
>                             =
>                             ((n1 * d2) * d3 + (ZUZU + (n3 * d2) * d1), d1 * (d2 * d3))}
>              (multAssociative n2 d1 d3) Refl }=
>     ( ((n1 * d2) * d3 + ((n2 * d1) * d3 + (n3 * d2) * d1), d1 * (d2 * d3)) )
>   ={ replace {x = (n1 * d2) * d3 + ((n2 * d1) * d3 + (n3 * d2) * d1)}
>              {y = ((n1 * d2) * d3 + (n2 * d1) * d3) + (n3 * d2) * d1}
>              {P = \ ZUZU => ((n1 * d2) * d3 + ((n2 * d1) * d3 + (n3 * d2) * d1), d1 * (d2 * d3))
>                             =
>                             (ZUZU, d1 * (d2 * d3))}
>              (plusAssociative ((n1 * d2) * d3) ((n2 * d1) * d3) ((n3 * d2) * d1)) Refl }=
>     ( (((n1 * d2) * d3 + (n2 * d1) * d3) + (n3 * d2) * d1, d1 * (d2 * d3)) )
>   ={ replace {x = (n3 * d2) * d1}
>              {y = n3 * (d2 * d1)}
>              {P = \ ZUZU => (((n1 * d2) * d3 + (n2 * d1) * d3) + (n3 * d2) * d1, d1 * (d2 * d3))
>                             =
>                             (((n1 * d2) * d3 + (n2 * d1) * d3) + ZUZU, d1 * (d2 * d3))}
>              (sym (multAssociative n3 d2 d1)) Refl }=         
>     ( (((n1 * d2) * d3 + (n2 * d1) * d3) + n3 * (d2 * d1), d1 * (d2 * d3)) )
>   ={ replace {x = (n1 * d2) * d3 + (n2 * d1) * d3}
>              {y = (n1 * d2 + n2 * d1) * d3}
>              {P = \ ZUZU => (((n1 * d2) * d3 + (n2 * d1) * d3) + n3 * (d2 * d1), d1 * (d2 * d3))
>                             =
>                             (ZUZU + n3 * (d2 * d1), d1 * (d2 * d3))}
>              (sym (multDistributesOverPlusLeft (n1 * d2) (n2 * d1) d3)) Refl }=
>     ( ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), d1 * (d2 * d3)) )
>   ={ replace {x = d1 * (d2 * d3)}
>              {y = (d1 * d2) * d3}
>              {P = \ ZUZU => ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), d1 * (d2 * d3))
>                             =
>                             ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), ZUZU)}
>              (multAssociative d1 d2 d3) Refl }=  
>     ( ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), (d1 * d2) * d3) )
>   ={ replace {x = d2 * d1}
>              {y = d1 * d2}
>              {P = \ ZUZU => ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), (d1 * d2) * d3)
>                             =
>                             ((n1 * d2 + n2 * d1) * d3 + n3 * (ZUZU), (d1 * d2) * d3)}
>              (multCommutative d2 d1) Refl }=
>     ( ((n1 * d2 + n2 * d1) * d3 + n3 * (d1 * d2), (d1 * d2) * d3) )
>   ={ Refl }=
>     ( (n1 * d2 + n2 * d1, d1 * d2) + (n3, d3) )
>   ={ Refl }=
>     ( ((n1, d1) + (n2, d2)) + (n3, d3) )
>   QED
> %freeze plusAssociative


> ||| Multiplication is commutative
> multCommutative : (x : Fraction) -> (y : Fraction) -> x * y = y * x
> multCommutative (n1, d1) (n2, d2) = 
>     ( (n1, d1) * (n2, d2) )
>   ={ Refl }=
>     ( (n1 * n2, d1 * d2) )
>   ={ replace {x = n1 * n2}
>              {y = n2 * n1}
>              {P = \ ZUZU => (n1 * n2, d1 * d2) = (ZUZU, d1 * d2)}
>              (Nat.multCommutative n1 n2) Refl }=
>     ( (n2 * n1, d1 * d2) )
>   ={ replace {x = d1 * d2}
>              {y = d2 * d1}
>              {P = \ ZUZU => (n2 * n1, d1 * d2) = (n2 * n1, ZUZU)}
>              (Nat.multCommutative d1 d2) Refl }=           
>     ( (n2 * n1, d2 * d1) )
>   ={ Refl }=
>     ( (n2, d2) * (n1, d1) )
>   QED
> %freeze multCommutative


> |||
> multOneRight : (x : Fraction) -> x * (fromInteger 1) = x
> multOneRight (n, d) = 
>     ( (n, d) * (S Z, S Z) )
>   ={ Refl }=
>     ( (n * (S Z), d * (S Z)) )
>   ={ replace {x = n * (S Z)}
>              {y = n}
>              {P = \ ZUZU => (n * (S Z), d * (S Z)) = (ZUZU, d * (S Z))}
>              (multOneRightNeutral n) Refl }=
>     ( (n, d * (S Z)) )
>   ={ replace {x = d * (S Z)}
>              {y = d}
>              {P = \ ZUZU => (n, d * (S Z)) = (n, ZUZU)}
>              (multOneRightNeutral d) Refl }=           
>     ( (n, d) )
>   QED
> %freeze multOneRight


> |||
> multOneLeft : (x : Fraction) -> (fromInteger 1) * x = x
> multOneLeft x = 
>     ( (fromInteger 1) * x )
>   ={ multCommutative (fromInteger 1) x }=
>     ( x * (fromInteger 1) )
>   ={ multOneRight x }=
>     ( x )
>   QED
> %freeze multOneLeft

> ---}
