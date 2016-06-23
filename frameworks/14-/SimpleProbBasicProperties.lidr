> module SimpleProbBasicProperties

> import Data.List

> import SimpleProb
> import SimpleProbBasicOperations
> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import ListOperations

> %default total
> %access public export
> %auto_implicits off


> |||
> toListLemma : {A : Type} -> (p : SimpleProb A) -> sumMapSnd (toList p) = 1
> toListLemma (MkSimpleProb _ prf) = prf


> {-

> ---}
