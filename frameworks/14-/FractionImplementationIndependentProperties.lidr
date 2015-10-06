> module FractionImplementationIndependentProperties


> import FractionSpecification


> %default total


The following does not type check! 

> instance Num Fraction where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat

The error message is "Overlapping instance: Num Integer already
defined". Am I missing something obvious here? Is this an Idris bug?


