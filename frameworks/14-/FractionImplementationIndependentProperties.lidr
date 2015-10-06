> module FractionImplementationIndependentProperties


> import FractionSpecification


> %default total


The following does not type check! 

> instance Num Fraction where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat

The error message is "Overlapping instance: Num Integer already
defined". I guess this is because of the missing implementations of
|Fraction|, |plus|, |mult| and |fromNat|. 

But there should probably be a way to express the idea that |plus|,
|mult| and |fromNat| are in fact sufficient (with a little help from
|fromIntegerNat|) to make |Fraction| and instance of |Num|.


