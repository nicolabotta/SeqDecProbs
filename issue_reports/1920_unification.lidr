> import Data.Vect

> %default total 

> Dec1 : {A : Type} -> (P : A -> Type) -> Type
> Dec1 {A} P = (a : A) -> Dec (P a) 

> filter : {A : Type} ->
>          {P : A -> Type} ->
>          Dec1 P ->
>          Vect n A -> 
>          (m : Nat ** Vect m A)
> filter d1P Nil = (Z ** Nil)
> filter d1P (a :: as) with (filter d1P as)
>   | (n ** as') with (d1P a)
>     | (Yes _) = (S n ** a :: as')
>     | (No  _) = (n ** as')

> filterSpec : {A : Type} ->
>              {P : A -> Type} ->
>              (d1P : Dec1 P) ->
>              (a : A) ->
>              (as : Vect n A) ->
>              Elem a as ->
>              (p : P a) ->
>              Elem a (getProof (filter d1P as))
> filterSpec {A} {P} d1P a Nil  Here       p impossible
> filterSpec {A} {P} d1P a Nil (There prf) p impossible
> filterSpec {A} {P} d1P a1 (a1 :: as) Here p with (filter d1P as)
>   | (n ** as') with (d1P a1)
>     | (Yes _) = Here {x = a1} {xs = as'}
>     | (No  contra) = void (contra p)
> filterSpec {A} {P} d1P a1 (a2 :: as) (There prf) p with (filter d1P as) proof itsEqual
>   | (n ** as') with (d1P a2)
>     | (Yes _) = -- There {x = a1} {xs = as'} {y = a2} (filterSpec d1P a1 as prf p)
>                 There {x = a1} {xs = as'} {y = a2} $
>                   replace {P=\rec => Elem a1 (getProof rec)} (sym itsEqual) $
>                     filterSpec {A} {P} d1P a1 as prf p
>     | (No  _) = -- filterSpec {A} {P} d1P a1 as prf p
>                 replace {P=\rec => Elem a1 (getProof rec)} (sym itsEqual) $
>                   filterSpec {P=P} d1P a1 as prf p

