> module TotalPreorder

> import Preorder

> %default total

> %access public export


> ||| TotalPreorder
> data TotalPreorder : Type -> Type where
>   MkTotalPreorder : {A : Type} ->
>                     (R : A -> A -> Type) ->
>                     (reflexive : (x : A) -> R x x) ->
>                     (transitive : (x : A) -> (y : A) -> (z : A) -> R x y -> R y z -> R x z) ->
>                     (totalPre : (x : A) -> (y : A) -> Either (R x y) (R y x)) ->
>                     TotalPreorder A
