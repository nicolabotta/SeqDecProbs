> module FractionProperties

> import Fraction
> import FractionOperations
> import FractionNormal
> import NatPositive


> %default total


> ||| Fraction is an instance of Num
> instance Num Fraction where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat


