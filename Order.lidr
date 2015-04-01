> module Order


> -- import Decidable.Order


> %default total 


> ||| Preorder on t
> class Preorder t where
>   total C : t -> t -> Type 
>   total reflexive : (x : t) -> C x x   
>   total transitive : (x : t) -> (y : t) -> (z : t) -> C x y -> C y z -> C x z


> ||| Total preorder on t
> class (Preorder t) => TotalPreorder t where
>   total either : (x : t) -> (y : t) -> Either (C x y) (C y x)       





> {-

> ||| Preorder
> data Preorder : {T : Type} -> (T -> T -> Type) -> Type where
>   MkPreorder : {T : Type} -> 
>                (R : T -> T -> Type) ->
>                (reflexive : (x : T) -> R x x) ->
>                (transitive : (x : T) -> (y : T) -> (z : T) -> R x y -> R y z -> R x z) ->
>                Preorder R


> ||| TotalPreorder
> data TotalPreorder : {T : Type} -> (T -> T -> Type) -> Type where
>   MkTotalPreorder : {T : Type} -> 
>                     (R : T -> T -> Type) ->
>                     (reflexive : (x : T) -> R x x) ->
>                     (transitive : (x : T) -> (y : T) -> (z : T) -> R x y -> R y z -> R x z) ->
>                     (autaut : (x : T) -> (y : T) -> Either (R x y) (R y x)) ->
>                     TotalPreorder R


> ||| Preorders on |A| induce preorders on |(A, B)|
> fromPreorder1 : {A, B : Type} -> {R : A -> A -> Type} ->
>           Preorder {T = A} R -> 
>           Preorder {T = (A, B)} (\ x => \ y => R (fst x) (fst y))
> fromPreorder1 (MkPreorder R reflexive transitive) = 
>   MkPreorder (\ x => \ y => R (fst x) (fst y))
>              (\ x => reflexive (fst x))
>              (\ x => \ y => \ z => \ xRy => \ yRz => transitive (fst x) (fst y) (fst z) xRy yRz)


> ||| Total preorders on |A| induce total preorders on |(A, B)|
> fromTotalPreorder1 : {A, B : Type} -> {R : A -> A -> Type} ->
>           TotalPreorder {T = A} R -> 
>           TotalPreorder {T = (A, B)} (\ x => \ y => R (fst x) (fst y))
> fromTotalPreorder1 (MkTotalPreorder R reflexive transitive autaut) = 
>   MkTotalPreorder (\ x => \ y => R (fst x) (fst y))
>              (\ x => reflexive (fst x))
>              (\ x => \ y => \ z => \ xRy => \ yRz => transitive (fst x) (fst y) (fst z) xRy yRz)
>              (\ x => \ y => autaut (fst x) (fst y))

> -}


> {-

> ||| Preorder on t
> data TotalPreorder : Type -> Type where
>   MkTotalPreorder : {A : Type} -> 
>                     (po : Preorder A) ->
>                     (autaut : (x : A) -> (y : A) -> Either (po.op x y) (po.op y x)) ->
>                     TotalPreorder A


> ||| Preorders on |t1| induce preorders on |(t1, t2)|
> fromLeft : {A, B : Type} -> Preorder A -> Preorder (A, B)
> fromLeft (MkPreorder op reflexive transitive) = 
>   MkPreorder (\ x => \ y => op (fst x) (fst y))
>              (\ x => reflexive (fst x))
>              (\ x => \ y => \ z => \ opxy => \ opyz => transitive (fst x) (fst y) (fst z) opxy opyz)

> -}


> {-

> ||| Preorder on t
> class Preorder (t : Type) (po : t -> t -> Type) where
>   total reflexive : (x : t) -> po x x   
>   total transitive : (x : t) -> (y : t) -> (z : t) -> po x y -> po y z -> po x z

> ||| Preorders on |t1| induce preorders on |(t1, t2)|
> instance Preorder t1 po => Preorder (t1, t2) (\ x => \ y => po (fst x) (fst y)) where
>     reflexive x = reflexive (fst x)
>     transitive x y z xy yz = transitive (fst x) (fst y) (fst z) xy yz

> -}


> {-

> ||| Preorder on t
> class Preorder t where
>   total PO : t -> t -> Type 
>   total reflexive : (x : t) -> PO x x   
>   total transitive : (x : t) -> (y : t) -> (z : t) -> PO x y -> PO y z -> PO x z


> ||| Total preorder on t
> class (Preorder t) => TotalPreorder t where
>   total autaut : (x : t) -> (y : t) -> Either (PO x y) (PO y x)       

> -}


> {-

> class (Preorder t to) => Preordered t (to : t -> t -> Type) | t where
>   total preorder : (a : t) -> (b : t) -> Either (to a b) (to b a)       

> -}
