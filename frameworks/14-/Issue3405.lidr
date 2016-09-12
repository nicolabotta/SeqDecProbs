> module Issue3405

> import SimpleProb
> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import NatPositive
> import Fraction
> import NumRefinements
> import FractionNormal
> import ListOperations
> import ListProperties

> %default total
> %access public export
> %auto_implicits off

> -- %logging 5

> normalize : {A : Type} -> SimpleProb A -> SimpleProb A
> normalize {A} (MkSimpleProb Nil sum) = MkSimpleProb Nil sum
> normalize {A} (MkSimpleProb (ap :: Nil) sum) = MkSimpleProb (ap :: Nil) sum
> normalize {A} (MkSimpleProb (ap :: ap' :: aps) sum) = MkSimpleProb aps' sum' where
>   aps' : List (A, NonNegRational)
>   aps' = discardBySndZero (ap :: ap' :: aps)
>   sum' : sumMapSnd aps' = 1
>   sum' = trans (discardBySndZeroLemma (ap :: ap' :: aps)) sum


