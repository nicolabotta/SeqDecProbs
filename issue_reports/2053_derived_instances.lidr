> import Decidable.Order

> instance Preorder a po => Preorder (a,b) (\ ab1 => \ ab2 => po (fst ab1) (fst ab2)) where
>   -- transitive x y z xpoy ypoz = transitive (fst x) (fst y) (fst z) xpoy ypoz
>   reflexive x = reflexive (fst x)
