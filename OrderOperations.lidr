> module PreorderOperations


> import Preorder


> %default total


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

> ||| Total preorders on |A| induce total preorders on |(A, B)|
> fromTotalPreorder1 : {A, B : Type} -> TotalPreorder A -> TotalPreorder (A, B)
> fromTotalPreorder1 (MkTotalPreorder R reflexive transitive totalPre) =
>   MkTotalPreorder (\ x => \ y => R (fst x) (fst y))
>              (\ x => reflexive (fst x))
>              (\ x => \ y => \ z => \ xRy => \ yRz => transitive (fst x) (fst y) (fst z) xRy yRz)
>              (\ x => \ y => totalPre (fst x) (fst y))


> ||| Total preorders on |B| induce total preorders on |(A, B)|
> fromTotalPreorder2 : {A, B : Type} -> TotalPreorder B -> TotalPreorder (A, B)
> fromTotalPreorder2 (MkTotalPreorder R reflexive transitive totalPre) =
>   MkTotalPreorder (\ x => \ y => R (snd x) (snd y))
>              (\ x => reflexive (snd x))
>              (\ x => \ y => \ z => \ xRy => \ yRz => transitive (snd x) (snd y) (snd z) xRy yRz)
>              (\ x => \ y => totalPre (snd x) (snd y))


> {-

> fstType : (a -> a -> Type) -> ((a,b) -> (a,b) -> Type)
> fstType F ab1 ab2 = F (fst ab1) (fst ab2)


> sndType : (b -> b -> Type) -> ((a,b) -> (a,b) -> Type)
> sndType F ab1 ab2 = F (snd ab1) (snd ab2)

> -}
