> module SimpleProb

> import Syntax.PreorderReasoning

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties

> import NatPositive
> import FractionNormal
> import NumRefinements
> import NumProperties
> import FunOperations
> import ListProperties

> %default total
> %access public export
> %auto_implicits off


> %freeze sum
> %freeze cross
> %freeze mapSndMapCrossAnyIdLemma
> %freeze sumSingletonLemma

> |||
> data SimpleProb : Type -> Type where
>   MkSimpleProb : {alpha : Type} -> 
>                  (aps : List (alpha, NonNegRational)) ->
>                  sumMapSnd aps = 1 ->
>                  SimpleProb alpha

* Operations

> |||
> list : {alpha : Type} -> SimpleProb alpha -> List (alpha, NonNegRational)
> list (MkSimpleProb aps _) = aps

> listLemma : {alpha : Type} -> (p : SimpleProb alpha) -> sumMapSnd (list p) = 1
> listLemma (MkSimpleProb _ prf) = prf

> ||| 
> prob : {alpha : Type} -> (Eq alpha) => SimpleProb alpha -> alpha -> NonNegRational
> prob (MkSimpleProb aps _) a = foldr f 0 aps where
>   f : (alpha, NonNegRational) -> NonNegRational -> NonNegRational
>   f (a', p') p = if (a == a') then p + p' else p


* Properties

|SimpleProb| is a functor:

> fmap : {A, B : Type} -> (A -> B) -> SimpleProb A -> SimpleProb B
> fmap f (MkSimpleProb aps p) = 
>   MkSimpleProb (map (cross f id) aps) s4 where
>     s1 : map snd (map (cross f id) aps) = map snd aps
>     s1 = mapSndMapCrossAnyIdLemma f aps
>     s2 : sumMapSnd (map (cross f id) aps) = sumMapSnd aps
>     s2 = cong s1
>     s3 : sumMapSnd aps = 1
>     s3 = p
>     s4 : sumMapSnd (map (cross f id) aps) = 1
>     s4 = trans s2 s3


|SimpleProb| is a monad:

> ret : {A : Type} -> A -> SimpleProb A
> ret {A} a = MkSimpleProb aps s1 where
>   aps : List (A, NonNegRational)
>   aps = [(a, 1)]
>   s1  : sumMapSnd aps = 1
>   s1  = sumSingletonLemma 1


> |||
> bind : {A, B : Type} -> SimpleProb A -> (A -> SimpleProb B) -> SimpleProb B
> bind {A} {B} (MkSimpleProb aps prf) f = MkSimpleProb bps' prf' where
>   f' : A -> List (B, NonNegRational)
>   f' a = list (f a)
>   prfs' : (a : A) -> sumMapSnd (f' a) = 1
>   prfs' a = listLemma (f a)
>   bps' : List (B, NonNegRational)
>   bps' = mvMult aps f'  
>   prf' : sumMapSnd bps' = 1
>   prf' = ( sumMapSnd bps' )
>        ={ Refl }=
>          ( sumMapSnd (mvMult aps f') )
>        ={ mvMultLemma aps f' prfs' }=
>          ( sumMapSnd aps )
>        ={ prf }=
>          ( 1 )
>        QED  


> {-

> ---}
