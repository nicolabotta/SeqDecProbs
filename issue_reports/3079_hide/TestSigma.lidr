> module VectOperations


> import Data.Vect
> -- import Data.Fin
> -- import Data.So

> import Decidable
> -- import TotalPreorder
> -- import TotalPreorderOperations
> -- import NatProperties
> import Sigma


> %default total

> %access public export


Lookup

> ||| Lookup the index of an element of a vector
> lookup : {A : Type} -> .(a : A) -> .(as : Vect n A) -> Elem a as -> Fin n
> lookup {n = Z}   a  Nil        Here         impossible
> lookup {n = Z}   a  Nil       (There p)     impossible
> lookup {n = S m} a (a :: as)   Here       = FZ
> lookup {n = S m} a (a' :: as) (There prf) = FS (lookup a as prf)

> filter : {A : Type} ->
>          {P : A -> Type} ->
>          Dec1 P ->
>          Vect n A -> 
>          Sigma Nat (\ m => Vect m A)
> filter d1P Nil = MkSigma Z Nil
> filter d1P (a :: as) with (filter d1P as)
>   | (MkSigma n as') with (d1P a)
>     | (Yes _) = MkSigma (S n) (a :: as')
>     | (No  _) = MkSigma n as'
