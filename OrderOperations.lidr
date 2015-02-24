> module OrderOperations


> import Decidable.Order

> import Order


> %default total 


> fstType : (a -> a -> Type) -> ((a,b) -> (a,b) -> Type)
> fstType F ab1 ab2 = F (fst ab1) (fst ab2)


> sndType : (b -> b -> Type) -> ((a,b) -> (a,b) -> Type)
> sndType F ab1 ab2 = F (snd ab1) (snd ab2)


