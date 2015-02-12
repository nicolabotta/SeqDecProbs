> module VectOperations


> import Data.Vect
> import Data.Fin

> import Decidable


> %default total


> ||| Lookup the index of an element of a vector
> lookup : {A : Type} -> (a : A) -> (as : Vect n A) -> Elem a as -> Fin n
> lookup {n = Z}   a  Nil        Here         impossible
> lookup {n = Z}   a  Nil       (There p)     impossible
> lookup {n = S m} a (a :: as)   Here       = FZ
> lookup {n = S m} a (a' :: as) (There prf) = FS (lookup a as prf)


> ||| Filters a vector on a decidable property and pairs elements with proofs
> filterTag : {A : Type} ->
>             {P : A -> Type} ->
>             Dec1 P ->
>             Vect n A -> 
>             (m : Nat ** Vect m (Sigma A P))
> filterTag d1P Nil = (Z ** Nil)
> filterTag d1P (a :: as) with (filterTag d1P as)
>   | (_ ** tail) with (d1P a)
>     | (Yes p)     = (_ ** (a ** p) :: tail)
>     | (No contra) = (_ ** tail)


