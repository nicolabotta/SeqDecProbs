> module Ops

> import Data.Vect
> import Data.So
> import Data.Fin

> import BoundedNat.Blt
> import Nat.Postulates
> import Nat.Properties


> %default total

> %access public export


> nubbedBy : (alpha -> alpha -> Bool) -> Vect n alpha -> Bool
> nubbedBy {n} p v = n == (fst (nubBy p v))

> idx : Vect n alpha -> Blt n -> alpha
> idx {n = Z}    Nil       b = void (ltZ_bot (snd b))
> idx {n = S m} (a :: as) (Z ** _) = a
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
>       So (elemBy p a as) ->
>       Blt n
> xdi p a as q = (fromMaybe Z m ** believe_me Oh) where
>   m : Maybe Nat
>   m = map finToNat (findIndex (p a) as)
