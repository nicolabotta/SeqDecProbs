> module TotalPreorderOperations

> import TotalPreorder

> %default total

> %access public export


> ||| R
> R : {A : Type} -> TotalPreorder A -> (A -> A -> Type)
> R (MkTotalPreorder R _ _ _) = R


> ||| reflexive
> reflexive : {A : Type} ->
>             (tp : TotalPreorder A) ->
>             (x : A) -> (R tp) x x
> reflexive (MkTotalPreorder _ reflexive _ _) = reflexive


> ||| transitive
> transitive : {A : Type} ->
>              (tp : TotalPreorder A) ->
>              (x : A) -> (y : A) -> (z : A) -> (R tp) x y -> (R tp) y z -> (R tp) x z
> transitive (MkTotalPreorder _ _ transitive _) = transitive


> ||| totalPre
> totalPre : {A : Type} ->
>          (tp : TotalPreorder A) ->
>          (x : A) -> (y : A) -> Either ((R tp) x y) ((R tp) y x)
> totalPre (MkTotalPreorder _ _ _ totalPre) = totalPre


> ||| Total preorders on |A| induce total preorders on |(A, B)|
> fromTotalPreorder1 : {A, B : Type} -> TotalPreorder A -> TotalPreorder (A, B)
> fromTotalPreorder1 (MkTotalPreorder R reflexive transitive totalPre) =
>   MkTotalPreorder (\ x => \ y => R (fst x) (fst y))
>              (\ x => reflexive (fst x))
>              (\ x => \ y => \ z => \ xRy => \ yRz => transitive (fst x) (fst y) (fst z) xRy yRz)
>              (\ x => \ y => totalPre (fst x) (fst y))


> from2 : {A, B : Type} -> (B -> B -> Type) -> (A, B) -> (A, B) -> Type
> from2 R x y = R (snd x) (snd y)

> ||| Total preorders on |B| induce total preorders on |(A, B)|
> fromTotalPreorder2 : {A, B : Type} -> TotalPreorder B -> TotalPreorder (A, B)
> fromTotalPreorder2 to =
>   MkTotalPreorder (from2 (R to))
>                   (\ x => reflexive to (snd x))
>                   (\ x => \ y => \ z => \ xRy => \ yRz => transitive to (snd x) (snd y) (snd z) xRy yRz)
>                   (\ x => \ y => totalPre to (snd x) (snd y))
