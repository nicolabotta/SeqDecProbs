> class Preorder t where
>   total PO : t -> t -> Type 
>   total reflexive : (x : t) -> PO x x   
>   total transitive : (x : t) -> (y : t) -> (z : t) -> PO x y -> PO y z -> PO x z

> namespace lala
>   instance Preorder t1 => Preorder (t1, t2) where
>     PO x y = PO (fst x) (fst y)
>     reflexive x = reflexive (fst x)
>     transitive x y z xy yz = transitive (fst x) (fst y) (fst z) xy yz

> namespace lula
>   instance Preorder t2 => Preorder (t1, t2) where
>     PO x y = PO (snd x) (snd y)
>     reflexive x = reflexive (snd x)
>     transitive x y z xy yz = transitive (snd x) (snd y) (snd z) xy yz


