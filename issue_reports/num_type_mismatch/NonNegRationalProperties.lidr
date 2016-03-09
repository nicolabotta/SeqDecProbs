> module NonNegRationalProperties


> import NonNegRational
> import NonNegRationalOperations
> import Fraction
> import FractionNormal
> import NatPositive


> %default total
> %access public export


> ||| NonNegRational is an implementation of Show
> implementation Show NonNegRational where
>   show q = show (num q) ++ "/" ++ show (den q)


> ||| NonNegRational is an implementation of Num
> implementation Num NonNegRational where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat


