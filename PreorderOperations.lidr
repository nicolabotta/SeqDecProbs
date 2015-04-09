> module PreorderOperations


> import Preorder


> %default total 


> ||| R
> R : {A : Type} -> Preorder A -> (A -> A -> Type)
> R (MkPreorder R _ _) = R


> ||| reflexive
> reflexive : {A : Type} -> 
>             (tp : Preorder A) -> 
>             (x : A) -> (R tp) x x
> reflexive (MkPreorder _ reflexive _) = reflexive


> ||| transitive
> transitive : {A : Type} -> 
>              (tp : Preorder A) -> 
>              (x : A) -> (y : A) -> (z : A) -> (R tp) x y -> (R tp) y z -> (R tp) x z
> transitive (MkPreorder _ _ transitive) = transitive


> ||| Preorders on |A| induce preorders on |(A, B)|
> fromPreorder1 : {A, B : Type} -> Preorder A -> Preorder (A, B)
> fromPreorder1 (MkPreorder R reflexive transitive) = 
>   MkPreorder (\ x => \ y => R (fst x) (fst y))
>              (\ x => reflexive (fst x))
>              (\ x => \ y => \ z => \ xRy => \ yRz => transitive (fst x) (fst y) (fst z) xRy yRz)

> ||| Preorders on |B| induce preorders on |(A, B)|
> fromPreorder2 : {A, B : Type} -> Preorder B -> Preorder (A, B)
> fromPreorder2 (MkPreorder R reflexive transitive) = 
>   MkPreorder (\ x => \ y => R (snd x) (snd y))
>              (\ x => reflexive (snd x))
>              (\ x => \ y => \ z => \ xRy => \ yRz => transitive (snd x) (snd y) (snd z) xRy yRz)

