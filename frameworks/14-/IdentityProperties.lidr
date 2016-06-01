> module IdentityProperties


> import Control.Monad.Identity

> import IdentityOperations
> import Sigma
> import Decidable
> import Unique
> import Finite
> import UnitProperties


> %default total

> %access public export


> ||| Id is injective
> injectiveId : {a : Type} -> {left : a} -> {right : a} -> (Id left) = (Id right) -> left = right
> injectiveId Refl = Refl
> %freeze injectiveId -- frozen

Id is a container monad:

> |||
> elemNonEmptySpec0 : {A : Type} ->
>                     (a : A) -> (ia : Identity A) ->
>                     a `Elem` ia -> NonEmpty ia
> elemNonEmptySpec0 a (Id a) Refl = ()   
> %freeze elemNonEmptySpec0 -- frozen

> ||| 
> elemNonEmptySpec1 : {A : Type} ->
>                     (ia : Identity A) ->
>                     NonEmpty ia -> 
>                     Sigma A (\ a => a `Elem` ia)
> elemNonEmptySpec1 (Id a) _ = (MkSigma a Refl)
> %freeze elemNonEmptySpec1 -- frozen


Container monad decidability:

> ||| |Elem| is decidable
> decElem : {A : Type} -> DecEq0 A -> (a : A) -> (ma : Identity A) -> Dec (a `Elem` ma)
> decElem dec a1 (Id a2) with (dec a1 a2)
>   | (Yes prf)   = Yes prf
>   | (No contra) = No contra
> %freeze decElem -- frozen


Container monad uniqueness:

> ||| |Elem| is unique
> uniqueElem : {A : Type} -> UniqueEq0 A -> (a : A) -> (ma : Identity A) -> Unique (a `Elem` ma)
> uniqueElem unique a1 (Id a2) p q = unique a1 a2 p q
> %freeze uniqueElem -- frozen


Show

> using (A : Type)
>   implementation (Show A) => Show (Identity A) where
>     show (Id a) = show a


Specific container monad properties

> ||| Values of type |Identity A| are never empty
> nonEmptyLemma : {A : Type} -> 
>                 (ia : Identity A) -> 
>                 NonEmpty ia
> nonEmptyLemma (Id a) = elemNonEmptySpec0 a (Id a) Refl                
> %freeze nonEmptyLemma -- frozen

> ||| All is finite
> finiteAll : {A : Type} -> {P : A -> Type} ->
>             Finite1 P -> (ia : Identity A) -> Finite (All P ia)
> finiteAll f1P (Id a) = f1P a
> %freeze finiteAll -- frozen

> ||| NotEmpty is finite
> finiteNonEmpty : {A : Type} -> (ia : Identity A) -> Finite (NonEmpty ia)
> finiteNonEmpty _ = finiteUnit
> %freeze finiteNonEmpty -- frozen


> {-

> ---}
