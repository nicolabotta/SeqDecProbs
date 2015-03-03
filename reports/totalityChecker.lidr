> import Data.Fin
> import Data.Vect

> total
> Dec1 : {A : Type} -> (P : A -> Type) -> Type
> Dec1 {A} P = (a : A) -> Dec (P a) 

> instance Uninhabited (Elem {a} x Nil) where
>   uninhabited Here impossible                                                                                          
>   uninhabited (There p) impossible      

> total
> filter : {A : Type} ->
>          {P : A -> Type} ->
>          Dec1 P ->
>          Vect n A -> 
>          (m : Nat ** Vect m A)
> filter d1P Nil = (Z ** Nil)
> filter d1P (a :: as) with (filter d1P as)
>   | (_ ** tail) with (d1P a)
>     | (Yes p)     = (_ ** a :: tail)
>     | (No contra) = (_ ** tail)

> total
> filterLemma : {A : Type} ->
>               {P : A -> Type} ->
>               (d1P : Dec1 P) ->
>               (a : A) ->
>               (as : Vect n A) ->
>               Elem a as ->
>               (p : P a) ->
>               Elem a (getProof (filter d1P as))
> filterLemma d1P a Nil  prf       p = absurd prf -- impossible


