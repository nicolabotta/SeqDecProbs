> module Order


> -- import Decidable.Order


> %default total


> ||| Preorder
> data Preorder : Type -> Type where
>   MkPreorder : {T : Type} ->
>                (R : T -> T -> Type) ->
>                (reflexive : (x : T) -> R x x) ->
>                (transitive : (x : T) -> (y : T) -> (z : T) -> R x y -> R y z -> R x z) ->
>                Preorder T


> ||| TotalPreorder
> data TotalPreorder : Type -> Type where
>   MkTotalPreorder : {T : Type} ->
>                     (R : T -> T -> Type) ->
>                     (reflexive : (x : T) -> R x x) ->
>                     (transitive : (x : T) -> (y : T) -> (z : T) -> R x y -> R y z -> R x z) ->
>                     (totalPre : (x : T) -> (y : T) -> Either (R x y) (R y x)) ->
>                     TotalPreorder T


> {-

> ||| Preorder on t
> class Preorder t where
>   total C : t -> t -> Type
>   total reflexive : (x : t) -> C x x
>   total transitive : (x : t) -> (y : t) -> (z : t) -> C x y -> C y z -> C x z


> ||| Total preorder on t
> class (Preorder t) => TotalPreorder t where
>   total totalPre : (x : t) -> (y : t) -> Either (C x y) (C y x)

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

> class (Preorder t to) => Preordered t (to : t -> t -> Type) | t where
>   total preorder : (a : t) -> (b : t) -> Either (to a b) (to b a)

> -}
