> module Ops


> import BoundedNat.Blt
> import Nat.Postulates


> %default total


> nubbedBy : (alpha -> alpha -> Bool) -> Vect n alpha -> Bool
> nubbedBy {n} p v = n == (getWitness (nubBy p v))

> idx : Vect n alpha -> Blt n -> alpha
> idx {n = 0} Nil b impossible
> idx (a :: as) (Z ** _) = a
> idx {n = S m} (a :: as) (S k ** q) = idx {n = m} as (k ** lemma5  q)

> idx1 : Vect n alpha -> Blt n -> alpha
> idx1 = idx

> idx2 : Vect m (Vect n alpha) -> 
>        (i : Blt m) -> 
>        (j : Blt n) -> 
>        alpha
> idx2 xss i j = idx1 (idx1 xss i) j


> xdi : (p : alpha -> alpha -> Bool) ->
>       (a : alpha) ->
>       (as : Vect n alpha) -> 
>       so (elemBy p a as) ->
>       Blt n
> xdi p a as q = (fromMaybe Z (findIndex (p a) as) ** believe_me oh)
