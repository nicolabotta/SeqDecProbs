> namespace lala
>   class Preorder t where
>     total PO : t -> t -> Type 
>     total reflexive : (x : t) -> PO x x   
>     total transitive : (x : t) -> (y : t) -> (z : t) -> PO x y -> PO y z -> PO x z

> {-

> namespace lula
>   class Preorder t where
>     total PO : t -> t -> Type 
>     total reflexive : (x : t) -> PO x x   
>     total transitive : (x : t) -> (y : t) -> (z : t) -> PO x y -> PO y z -> PO x z

> -}

