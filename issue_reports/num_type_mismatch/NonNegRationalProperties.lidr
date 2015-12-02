> module NonNegRationalProperties


> import NonNegRational
> import NonNegRationalOperations
> import Fraction
> import FractionNormal
> import NatPositive


> %default total


> ||| NonNegRational is an instance of Show
> instance Show NonNegRational where
>   show q = show (num q) ++ "/" ++ show (den q)


> ||| NonNegRational is an instance of Num
> instance Num NonNegRational where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat


