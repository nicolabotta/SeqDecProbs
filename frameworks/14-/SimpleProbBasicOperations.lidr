> module SimpleProbBasicOperations

> import Data.List

> import SimpleProb
> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import NatPositive
> import FractionNormal
> import NumRefinements
> import FunOperations
> import ListOperations
> import ListProperties

> %default total
> %access public export
> %auto_implicits off


> |||
> toList : {A : Type} -> SimpleProb A -> List (A, NonNegRational)
> toList (MkSimpleProb aps _) = aps


> |||
> normalize : {A : Type} -> SimpleProb A -> SimpleProb A
> normalize {A} (MkSimpleProb aps sum) = (MkSimpleProb aps' sum') where
>   aps' : List (A, NonNegRational)
>   aps' = discardBySndZero aps
>   sum' : sumMapSnd aps' = 1
>   sum' = trans (discardBySndZeroLemma aps) sum


> |||
> support : {A : Type} -> SimpleProb A -> List A
> support sp = map fst (toList (normalize sp))


> |||
> probs : {A : Type} -> SimpleProb A -> List NonNegRational
> probs sp = map snd (toList (normalize sp))


> ||| 'prob sp a' is the probability of 'a' according to 'sp'
> prob : {A : Type} -> (Eq A) => SimpleProb A -> A -> NonNegRational
> prob (MkSimpleProb aps _) a = foldr f 0 aps where
>   f : (A, NonNegRational) -> NonNegRational -> NonNegRational
>   f (a', p') p = if (a == a') then p + p' else p


> {-

> prob : {A : Type} -> (DecEq A) => SimpleProb A -> A -> NonNegRational
> prob {A} (MkSimpleProb aps _) a = foldr f 0 aps where
>   f : (A, NonNegRational) -> NonNegRational -> NonNegRational
>   f (a', p') p with (decEq a a') 
>     | (Yes _) = p + p' 
>     | (No _)  = p

> ---}    

