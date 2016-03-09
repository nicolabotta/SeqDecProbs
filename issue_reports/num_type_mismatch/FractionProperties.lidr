> module FractionProperties

> import Fraction
> import FractionOperations
> import FractionNormal
> import NatPositive


> %default total
> %access public export


> ||| Fraction is an instance of Num
> implementation Num Fraction where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat


