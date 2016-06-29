> module SimpleProbMonadicProperties

> import Data.List
> import Data.List.Quantifiers
> import Syntax.PreorderReasoning

> import SimpleProb
> import SimpleProbBasicOperations
> import SimpleProbBasicProperties
> import SimpleProbMonadicOperations
> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties

> import NatPositive
> import FractionNormal
> import NumRefinements
> import NumProperties
> import FunOperations
> import ListOperations
> import ListProperties
> import Unique
> import Finite

> %default total
> %access public export
> %auto_implicits off


* |SimpleProb| is a functor:

> |||
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


* |SimpleProb| is a monad:

> |||
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
>   f' a = toList (f a)
>   prfs' : (a : A) -> sumMapSnd (f' a) = 1
>   prfs' a = toListLemma (f a)
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


* |SimpleProb| is a container monad:

> |||
> containerMonadSpec3 : {A : Type} -> {P : A -> Type} ->
>                       (a : A) -> (sp : SimpleProb A) ->
>                       All P sp -> a `Elem` sp -> P a
> containerMonadSpec3 {A} {P} a sp allp elemp = ListProperties.containerMonadSpec3 a (support sp) allp elemp



* Specific container monad properties

> |||
> uniqueAllLemma : {A : Type} -> {P : A -> Type} -> 
>                  Unique1 P -> (sp : SimpleProb A) -> Unique (All P sp)
> uniqueAllLemma u1P sp = ListProperties.uniqueAllLemma u1P (support sp)

> |||
> finiteAll : {A : Type} -> {P : A -> Type} -> 
>             Finite1 P -> (sp : SimpleProb A) -> Finite (All P sp)
> finiteAll f1P sp = ListProperties.finiteAll f1P (support sp)

> ||| NotEmpty is finite
> finiteNonEmpty : {A : Type} -> (sp : SimpleProb A) -> Finite (SimpleProbMonadicOperations.NonEmpty sp)
> finiteNonEmpty sp = ListProperties.finiteNonEmpty (support sp)


> {-

> ---}
