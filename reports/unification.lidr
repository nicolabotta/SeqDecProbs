> import Data.Vect
> import Data.Fin

> %default total

> instance Uninhabited (Elem {a} x Nil) where
>   uninhabited Here impossible                                                                                          
>   uninhabited (There p) impossible      

> lookup : (x : t) -> (xs : Vect n t) -> Elem x xs -> Fin n
> lookup {n = Z}   x  Nil prf               = absurd prf
> lookup {n = S m} x (x :: xs)   Here       = FZ
> lookup {n = S m} x (x' :: xs) (There prf) = FS (lookup x xs prf)

> indexLookupLemma : (x : alpha) -> 
>                    (xs : Vect n alpha) ->
>                    (prf : Elem x xs) -> 
>                    index (lookup x xs prf) xs = x
> indexLookupLemma x  Nil        prf        = absurd prf
> indexLookupLemma x (x :: xs)   Here       = Refl
> indexLookupLemma x (x' :: xs) (There prf) = 
>   let ih = indexLookupLemma x xs prf in rewrite ih in Refl

> lookupIndexLemma : (k : Fin n) ->
>                    (xs : Vect n t) ->
>                    (prf : Elem (index k xs) xs) ->
>                    lookup (index k xs) xs prf = k
> lookupIndexLemma  k      Nil       prf        = absurd k
> lookupIndexLemma  FZ    (x :: xs)  Here        = Refl
> lookupIndexLemma (FS k) (x :: xs) (There prf) = 
>   let ih = lookupIndexLemma k xs prf in rewrite ih in Refl
