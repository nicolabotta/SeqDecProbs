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
>     s1p' = trans s1 (trans s7 s8) where
>       s1 : sumMapSnd aps' = sum (snd (unzip aps'))
>       s1 = sumMapSndUnzipLemma aps'
>       s2 : length as' = length ssp
>       s2 = tagElemPreservesLength ssp
>       s3 : length ssp = length psp
>       s3 = lengthSupportProbsLemma sp
>       s4 : length as' = length psp
>       s4 = trans s2 s3
>       s5 : unzip (zip as' psp) = (as', psp)
>       s5 = unzipZipLemma as' psp s4
>       s6 : snd (unzip aps') = psp
>       s6 = cong {f = snd} s5
>       s7 : sum (snd (unzip aps')) = sum psp
>       s7 = cong {f = sum} s6
>       s8 : sum psp = 1
>       s8 = sumProbsLemma sp


> {-

> ---}
