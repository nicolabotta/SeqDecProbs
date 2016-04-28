> module IdentityProperties


> import Control.Monad.Identity

> import IdentityOperations
> import Sigma
> import Decidable
> import Unique


> %default total

> %access public export


> ||| Id is injective
> injectiveId : {a : Type} -> {left : a} -> {right : a} -> (Id left) = (Id right) -> left = right
> injectiveId Refl = Refl


Id is a container monad:

> |||
> elemEmptySpec0 : {A : Type} ->
>                  (a : A) -> (ia : Identity A) ->
>                  a `Elem` ia -> Not (Empty ia)
> elemEmptySpec0 a (Id a) Refl = id   

> ||| 
> elemEmptySpec1 : {A : Type} ->
>                  (ia : Identity A) ->
>                  Not (Empty ia) -> 
>                  Sigma A (\ a => a `Elem` ia)
> elemEmptySpec1 (Id a) _ = (MkSigma a Refl)

> ||| Values of type |Identity A| are never empty
> notEmptyLemma : {A : Type} -> 
>                 (ia : Identity A) -> 
>                 Not (Empty ia)
> notEmptyLemma (Id a) = elemEmptySpec0 a (Id a) Refl                

Container monad decidability:

> ||| |Elem| is decidable
> decElem : {A : Type} -> DecEq0 A -> (a : A) -> (ma : Identity A) -> Dec (a `Elem` ma)
> decElem dec a1 (Id a2) with (dec a1 a2)
>   | (Yes prf)   = Yes prf
>   | (No contra) = No contra

Container monad uniqueness:

> ||| |Elem| is unique
> uniqueElem : {A : Type} -> UniqueEq0 A -> (a : A) -> (ma : Identity A) -> Unique (a `Elem` ma)
> uniqueElem unique a1 (Id a2) p q = unique a1 a2 p q

Show

> using (A : Type)
>   implementation (Show A) => Show (Identity A) where
>     show (Id a) = show a
