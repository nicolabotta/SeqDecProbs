> class Preorder t (po : t -> t -> Type) where                                                                              
>   total transitive : (a : t) -> (b : t) -> (c : t) -> po a b -> po b c -> po a c                                          
>   total reflexive : (a : t) -> po a a   

> instance Preorder a po => Preorder (a,b) (\ ab1 => \ ab2 => po (fst ab1) (fst ab2)) where
>   transitive x y z xpoy ypoz = transitive (fst x) (fst y) (fst z) xpoy ypoz
>   reflexive x = reflexive (fst x)
