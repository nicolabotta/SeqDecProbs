> module FinOperations

> import Data.Fin
> import Data.Vect


> %default total


> ||| 'Tail' of a finite function
> tail : {A : Type} -> {n : Nat} ->
>        (Fin (S n) -> A) -> (Fin n -> A)
> -- tail f k = f (FS k)
> tail f = f . FS


> ||| Maps a finite function to a vector
> toVect : {A : Type} -> {n : Nat} ->
>          (Fin n -> A) -> Vect n A
> toVect {n =   Z} _ = Nil
> toVect {n = S m} f = (f FZ) :: (toVect (tail f))
> -- toVect f = map f range 

> ||| Sum of the values of a finite function
> sum : {n : Nat} -> (Fin n -> Nat) -> Nat
> sum {n = Z}   f = Z
> sum {n = S m} f = f FZ + sum (tail f)
