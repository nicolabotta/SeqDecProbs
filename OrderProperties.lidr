> module OrderProperties


> -- import Decidable.Order

> import Order
> -- import OrderOperations


> %default total


> {-

> ||| Preorders on |a| induce preorders on |(a, b)|
> instance [fstPreorder] Preorder a => Preorder (a, b) where
>   C x y = C (fst x) (fst y)
>   reflexive x = reflexive (fst x)
>   transitive x y z xy yz = transitive (fst x) (fst y) (fst z) xy yz


> ||| Preorders on |b| induce preorders on |(a, b)|
> instance [sndPreorder] Preorder b => Preorder (a, b) where
>   C x y = C (snd x) (snd y)
>   reflexive x = reflexive (snd x)
>   transitive x y z xy yz = transitive (snd x) (snd y) (snd z) xy yz


> ||| Total preorders on |a| induce total preorders on |(a, b)|
> instance TotalPreorder a => TotalPreorder (a, b) where
>   totalPre x y = s1 where
>     s1 : Either (C @{fstPreorder} x y) (C @{fstPreorder} y x)
>     s1= ?lala

> -}


> {-

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
