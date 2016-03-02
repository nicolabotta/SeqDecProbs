> module SimpleProb2986

> import NonNegRational
> import NonNegRationalOperations
> import NonNegRationalProperties

> import NatPositive
> import FractionNormal
> import NumRefinements
> import NumProperties
> import FunOperations
> import ListProperties

> %default total
> %access public export

> data SimpleProb : Type -> Type where
>   MkSimpleProb : {alpha : Type} -> 
>                  (aps : List (alpha, NonNegRational)) ->
>                  sum (map snd aps) = 1 ->
>                  SimpleProb alpha

> prob : (Eq alpha) => SimpleProb alpha -> alpha -> NonNegRational
> prob (MkSimpleProb aps _) a = foldr f 0 aps where
>   f : (alpha, NonNegRational) -> NonNegRational -> NonNegRational
>   f (a', p') p = if (a == a') then p + p' else p
> %freeze prob

> fmap : {A, B : Type} -> (A -> B) -> SimpleProb A -> SimpleProb B
> fmap f (MkSimpleProb aps p) = MkSimpleProb (map (cross f id) aps) ?lula 
