> module SimpleProbMeasures

> import SimpleProb
> import SimpleProbBasicOperations
> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import ListOperations

> -- postulate monotoneAverage
> import NonNegRationalPredicates
> import SimpleProbMonadicOperations

> %default total
> %access public export
> %auto_implicits off


> |||
> average : SimpleProb NonNegRational -> NonNegRational
> average = sumProds . toList 


> ||| |average| is monotone
> postulate monotoneAverage : {A : Type} ->
>                             (f : A -> NonNegRational) -> (g : A -> NonNegRational) ->
>                             (p : (a : A) -> f a `LTE` g a) ->
>                             (as : SimpleProb A) ->
>                             average (fmap f as) `LTE` average (fmap g as) 
