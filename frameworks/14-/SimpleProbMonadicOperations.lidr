> module SimpleProbMonadicOperations

> import Data.List
> import Data.List.Quantifiers
> import Syntax.PreorderReasoning

> import SimpleProb
> import SimpleProbBasicOperations
> import SimpleProbBasicProperties
> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import NatPositive
> import FractionNormal
> import NumRefinements
> import FunOperations
> import ListOperations
> import ListProperties
> import Sigma

> %default total
> %access public export
> %auto_implicits off


* |SimpleProb| is a functor:

> |||
> fmap : {A, B : Type} -> (A -> B) -> SimpleProb A -> SimpleProb B
> fmap f (MkSimpleProb aps s1p) = MkSimpleProb aps' s1p' where
>   aps' : List (B, NonNegRational)
>   aps' = map (cross f id) aps
>   s1p' : sumMapSnd aps' = 1
>   s1p' = ( sumMapSnd aps' )
>        ={ Refl }=
>          ( sum (map snd aps') )
>        ={ cong (mapSndMapCrossAnyIdLemma f aps) }=
>          ( sum (map snd aps) )
>        ={ Refl }=
>          ( sumMapSnd aps )
>        ={ s1p }=
>          ( 1 )
>        QED


* |SimpleProb| is a monad:

> |||
> ret : {A : Type} -> A -> SimpleProb A
> ret {A} a = MkSimpleProb [(a, 1)] (sumMapSndSingletonLemma a 1)

> |||
> bind : {A, B : Type} -> SimpleProb A -> (A -> SimpleProb B) -> SimpleProb B
> bind {A} {B} (MkSimpleProb aps s1p) f = MkSimpleProb bps' s1p' where
>   f' : A -> List (B, NonNegRational)
>   f' a = toList (f a)
>   s1ps' : (a : A) -> sumMapSnd (f' a) = 1
>   s1ps' a = toListLemma (f a)
>   bps' : List (B, NonNegRational)
>   bps' = mvMult aps f'  
>   s1p' : sumMapSnd bps' = 1
>   s1p' = ( sumMapSnd bps' )
>        ={ Refl }=
>          ( sumMapSnd (mvMult aps f') )
>        ={ mvMultLemma aps f' s1ps' }=
>          ( sumMapSnd aps )
>        ={ s1p }=
>          ( 1 )
>        QED


* |SimpleProb| is a container monad:

> |||
> Elem : {A : Type} -> A -> SimpleProb A -> Type
> Elem a sp = Elem a (support sp)

> |||
> NonEmpty : {A : Type} -> SimpleProb A -> Type
> NonEmpty sp = ListOperations.NonEmpty (support sp) 

> |||
> All : {A : Type} -> (P : A -> Type) -> SimpleProb A -> Type
> All P sp = All P (support sp) 

> ||| Tagging
> tagElem  :  {A : Type} -> (sp : SimpleProb A) -> SimpleProb (Sigma A (\ a => a `Elem` sp))
> tagElem sp = MkSimpleProb aps' s1p' where
>     ssp  : List A
>     ssp  = support sp
>     psp  : List NonNegRational
>     psp  = probs sp
>     as'  : List (Sigma A (\ a => a `Elem` sp))
>     as'  = ListOperations.tagElem ssp
>     aps' : List (Sigma A (\ a => a `Elem` sp), NonNegRational)
>     aps' = zip as' psp
>     s1p' : sumMapSnd aps' = 1
>     s1p' = ?lala 




> {-



> ||| Tagging
> tagElem  :  {A : Type} -> (sp : SimpleProb A) -> SimpleProb (Sigma A (\ a => a `Elem` sp))
> tagElem {A} sp = MkSimpleProb aps' prf' where
>   aps' : List ((Sigma A (\ a => a `Elem` sp)), NonNegRational)
>   aps' = map f (ListOperations.tagElem (support sp)) where
>     f : (Sigma A (\ a => a `Elem` sp)) -> ((Sigma A (\ a => a `Elem` sp)), NonNegRational)
>     f (MkSigma a prf) = (MkSigma a prf, prob sp a)
>   prf' : sumMapSnd aps' = 1
>   prf' = ?kiku

> ---}
