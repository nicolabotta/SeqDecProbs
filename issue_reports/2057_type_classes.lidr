> class Preorder t where
>   total po : t -> t -> Type 
>   total reflexive : (a : t) -> po a a   
>   total transitive : (a : t) -> (b : t) -> (c : t) -> po a b -> po b c -> po a c                                          

> instance Preorder a => Preorder (a,b) where
>   po a1b1 a2b2 = po (fst a1b1) (fst a2b2)
>   reflexive ab = reflexive (fst ab)
>   transitive a1b1 a2b2 a3b3 a1poa2 a2poa3 = transitive (fst a1b1) (fst a2b2) (fst a3b3) a1poa2 a2poa3

 
