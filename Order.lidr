> module Order


> import Decidable.Order


> %default total 


> class (Preorder t to) => Preordered t (to : t -> t -> Type) | t where
>   total preorder : (a : t) -> (b : t) -> Either (to a b) (to b a)       


