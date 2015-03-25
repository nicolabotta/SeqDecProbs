> module Order


> -- import Decidable.Order


> %default total 


> ||| Preorder on t
> class Preorder (t : Type) (po : t -> t -> Type) where
>   total reflexive : (x : t) -> po x x   
>   total transitive : (x : t) -> (y : t) -> (z : t) -> po x y -> po y z -> po x z

> ||| Preorders on |t1| induce preorders on |(t1, t2)|
> instance Preorder t1 po => Preorder (t1, t2) (\ x => \ y => po (fst x) (fst y)) where
>     reflexive x = reflexive (fst x)
>     transitive x y z xy yz = transitive (fst x) (fst y) (fst z) xy yz




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
