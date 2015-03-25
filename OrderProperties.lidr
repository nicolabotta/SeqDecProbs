> module OrderProperties


> -- import Decidable.Order

> import Order
> -- import OrderOperations


> %default total 


> namespace lala

>   ||| Preorders on |t1| induce preorders on |(t1, t2)|
>   instance Preorder t1 => Preorder (t1, t2) where
>     PO x y = PO (fst x) (fst y)
>     reflexive x = reflexive (fst x)
>     transitive x y z xy yz = transitive (fst x) (fst y) (fst z) xy yz


>   ||| Total preorders on |t1| induce total preorders on |(t1, t2)|
>   instance (TotalPreorder t1) => TotalPreorder (t1, t2) where
>     autaut x y = autaut (fst x) (fst y)


> namespace lula

>   ||| Preorders on |t2| induce preorders on |(t1, t2)|
>   instance Preorder t2 => Preorder (t1, t2) where
>     PO x y = PO (snd x) (snd y)
>     reflexive x = reflexive (snd x)
>     transitive x y z xy yz = transitive (snd x) (snd y) (snd z) xy yz


>   ||| Total preorders on |t2| induce total preorders on |(t1, t2)|
>   instance (TotalPreorder t2) => TotalPreorder (t1, t2) where
>     autaut x y = autaut (snd x) (snd y)



> {-

> ||| Preorders on |a| induce preorders on |(a,b)|
> instance Preorder a po => Preorder (a,b) (fstType {a} {b} po) where
>   transitive x y z xpoy ypoz = transitive (fst x) (fst y) (fst z) xpoy ypoz
>   reflexive x = reflexive (fst x)


> ||| Total preorders on |a| induce total preorders on |(a,b)|
> instance Preordered a po => Preordered (a,b) (fstType {a} {b} po) where
>   preorder x y = preorder (fst x) (fst y)


> ||| Preorders on |b| induce preorders on |(a,b)|
> instance Preorder b po => Preorder (a,b) (sndType {a} {b} po) where
>   transitive x y z xpoy ypoz = transitive (snd x) (snd y) (snd z) xpoy ypoz
>   reflexive x = reflexive (snd x)


> ||| Total preorders on |b| induce total preorders on |(a,b)|
> instance Preordered b po => Preordered (a,b) (sndType {a} {b} po) where
>   preorder x y = preorder (snd x) (snd y)

> -}
