> import Data.Vect
> import Data.Fin
> %default total

> Dec1 : {A : Type} -> (P : A -> Type) -> Type
> Dec1 {A} P = (a : A) -> Dec (P a) 

> filterDec : {A : Type} -> {P : A -> Type} ->
>             Dec1 P -> Vect n A -> Sigma Nat (\m => Vect m A)
> filterDec dP Nil = (Z ** Nil)
> filterDec dP (a :: as) with (filterDec dP as)
>   | (n ** as') with (dP a)
>     | (Yes _) = (S n ** a :: as')
>     | (No  _) = (n ** as')

does not introduce duplicates. More precisely, I would like to prove the
following lemma:

> Injective1 : Vect n t -> Type
> Injective1 {n} xs = (i : Fin n) -> (j : Fin n) -> index i xs = index j xs -> i = j

> injectiveTailLemma1 : (xs : Vect (S n) t) -> Injective1 xs -> Injective1 (tail xs)

> injectiveFilterDecLemma : 
>   {A : Type} -> {P : A -> Type} -> {n : Nat} ->
>   (dP : Dec1 P) -> (as : Vect n A) ->
>   Injective1 as -> Injective1 (getProof (filterDec dP as))
> injectiveFilterDecLemma {A} {P} {n = Z}   dP  Nil      iNil = ?kiko
> injectiveFilterDecLemma {A} {P} {n = S m} dP (a :: as) iaas = s0 where
>   n'  : Nat
>   n'  = getWitness (filterDec dP (a :: as))
>   as' : Vect n' A
>   as' = getProof (filterDec dP (a :: as))
>   s0  : Injective1 as'
>   s0  i j p with (filterDec dP as) proof itsEqual
>     | (fn ** fas) with (dP a)
>       | (Yes _) = ?liku
>       | (No  _) = ?laka -- replace {P = \rec => Fin (getWitness rec)} (sym itsEqual)
>                         --  (injectiveFilterDecLemma dP as (injectiveTailLemma1 (a :: as) iaas) i j q)
