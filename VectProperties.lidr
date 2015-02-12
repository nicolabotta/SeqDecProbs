> module VectProperties


> import Data.Vect
> import Data.Vect.Quantifiers
> import Data.Fin

> import Prop
> import VectOperations
> import Decidable


> %default total


> instance Uninhabited (Elem {a} x Nil) where
>   uninhabited Here impossible                                                                                          
>   uninhabited (There p) impossible      


Indexing and lookup

> indexLemma : (k : Fin n) -> (xs : Vect n t) -> Elem (index k xs) xs 
> indexLemma {n = Z}       k   Nil      = absurd k
> indexLemma {n = S m}  FZ    (x :: xs) = Here
> indexLemma {n = S m} (FS k) (x :: xs) = There (indexLemma k xs)

> indexLookupLemma : (x : alpha) -> 
>                    (xs : Vect n alpha) ->
>                    (prf : Elem x xs) -> 
>                    index (lookup x xs prf) xs = x
> indexLookupLemma x  Nil        prf        = absurd prf
> indexLookupLemma x (x :: xs)   Here       = Refl
> indexLookupLemma x (x' :: xs) (There prf) = 
>   let ih = indexLookupLemma x xs prf in rewrite ih in Refl
> {-
> indexLookupLemma x (x' :: xs) (There prf) = trans s1 (trans s2 s3) where
>   s1 : index (lookup x (x' :: xs) (There prf)) (x' :: xs) 
>        = 
>        index (FS (lookup x xs prf)) (x' :: xs) 
>   s1 = Refl
>   s2 : index (FS (lookup x xs prf)) (x' :: xs) 
>        =
>        index (lookup x xs prf) xs
>   s2 = Refl
>   s3 : index (lookup x xs prf) xs
>        =
>        x
>   s3 = indexLookupLemma x xs prf
> -}

> {-
> lookupIndexLemma : (k : Fin n) ->
>                    (xs : Vect n t) ->
>                    (prf : Elem (index k xs) xs) ->
>                    lookup (index k xs) xs prf = k
> lookupIndexLemma  k      Nil       prf        = absurd k
> lookupIndexLemma  FZ    (x :: xs)  prf        = Refl
> lookupIndexLemma (FS k) (x :: xs) (There prf) = 
>   let ih = lookupIndexLemma k xs prf in rewrite ih in Refl
> {-
> lookupIndexLemma {n = S m} (FS k) (x :: xs) = trans s1 (trans s2 s4) where
>   s1 : lookup (index (FS k) (x :: xs)) (x :: xs) (indexLemma (FS k) (x :: xs)) 
>        =
>        lookup (index k xs) (x :: xs) (There (indexLemma k xs)) 
>   s1 = Refl
>   s2 : lookup (index k xs) (x :: xs) (There (indexLemma k xs)) 
>        =
>        FS (lookup (index k xs) xs (indexLemma k xs))
>   s2 = Refl
>   s3 : lookup (index k xs) xs (indexLemma k xs)
>        =
>        k
>   s3 = lookupIndexLemma k xs
>   s4 : FS (lookup (index k xs) xs (indexLemma k xs))
>        =
>        FS k
>   s4 = ?kika --cong FS s3
> -}
> -}


Membership, quantifiers:

> AnyExistsLemma : {A : Type} -> {P : A -> Prop} -> Any P as -> Exists P
> AnyExistsLemma (Here {x} px) = Evidence x px 
> AnyExistsLemma (There prf) = AnyExistsLemma prf

> ElemAnyLemma : {A : Type} -> {P : A -> Prop} -> P a -> Elem a as -> Any P as
> ElemAnyLemma p Here = Here p
> ElemAnyLemma p (There e) = There (ElemAnyLemma p e)

> decAny : {A : Type} -> {P : A -> Prop} -> Dec1 P -> Dec1 (Any P)
> decAny d1P = any d1P


Filtering

> filterTagLemma : {A : Type} ->
>                  {P : A -> Type} ->
>                  (d1P : Dec1 P) ->
>                  (a : A) ->
>                  (as : Vect n A) ->
>                  Elem a as ->
>                  (p : P a) ->
>                  Elem (a ** p) (getProof (filterTag d1P as))
