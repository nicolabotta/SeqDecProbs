> import Data.Vect
> import Data.Vect.Quantifiers
> import Data.Fin

> %default total

> instance Uninhabited (Elem {a} x Nil) where
>   uninhabited Here impossible                                                                                          
>   uninhabited (There p) impossible      

> lookup : {A : Type} -> 
>          (a : A) -> (as : Vect n A) -> Elem a as -> Fin n
> lookup a  Nil        prf        = absurd prf
> lookup a (a :: as)   Here       = FZ
> lookup a (a' :: as) (There prf) = FS (lookup a as prf)

> indexLookupLemma : {A : Type} -> 
>                    (x : A) -> (xs : Vect n A) -> (prf : Elem x xs) -> 
>                    index (lookup x xs prf) xs = x
> indexLookupLemma x  Nil        prf        = absurd prf
> indexLookupLemma x (x :: xs)   Here       = Refl
> indexLookupLemma x (x' :: xs) (There prf) = 
>   let ih = indexLookupLemma x xs prf in rewrite ih in Refl

> lookupIndexLemma : {A : Type} -> 
>                    (k : Fin n) -> (xs : Vect n A) -> (prf : Elem (index k xs) xs) ->
>                    lookup (index k xs) xs prf = k
> lookupIndexLemma  k      Nil       prf        = absurd prf
> lookupIndexLemma  FZ    (x :: xs)  Here       = Refl
> lookupIndexLemma  FZ    (x :: xs) (There prf) = ?lookupIndexLemma_meta1
> lookupIndexLemma (FS k) (x :: xs) (There prf) = 
>   let ih = lookupIndexLemma k xs prf in rewrite ih in Refl



