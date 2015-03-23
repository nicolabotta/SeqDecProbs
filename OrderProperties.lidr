> module OrderProperties


> import Decidable.Order

> import Order
> import OrderOperations


> %default total 


> -- ||| Preorders on |a| induce preorders on |(a,b)|
> instance Preorder a po => Preorder (a,b) (fstType {a} {b} po) where
>   transitive x y z xpoy ypoz = transitive (fst x) (fst y) (fst z) xpoy ypoz
>   reflexive x = reflexive (fst x)


> -- ||| Total preorders on |a| induce total preorders on |(a,b)|
> instance Preordered a po => Preordered (a,b) (fstType {a} {b} po) where
>   preorder x y = preorder (fst x) (fst y)


> -- ||| Preorders on |b| induce preorders on |(a,b)|
> instance Preorder b po => Preorder (a,b) (sndType {a} {b} po) where
>   transitive x y z xpoy ypoz = transitive (snd x) (snd y) (snd z) xpoy ypoz
>   reflexive x = reflexive (snd x)


> -- ||| Total preorders on |b| induce total preorders on |(a,b)|
> instance Preordered b po => Preordered (a,b) (sndType {a} {b} po) where
>   preorder x y = preorder (snd x) (snd y)


