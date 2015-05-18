> import Data.Vect

> %default total 

> Dec1 : {A : Type} -> (P : A -> Type) -> Type
> Dec1 {A} P = (a : A) -> Dec (P a) 

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

> filterTagLemma : {A : Type} ->
>                  {P : A -> Type} ->
>                  (d1P : Dec1 P) ->
>                  (a : A) ->
>                  (as : Vect n A) ->
>                  Elem a as ->
>                  (p : P a) ->
>                  Elem a (map Sigma.getWitness (getProof (filterTag d1P as)))

