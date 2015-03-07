> module FinOperations

> import Data.Fin
> import Data.Vect
 

> %default total


> ||| 'Tail' of a finite function
> tail : {A : Type} -> (Fin (S n) -> A) -> (Fin n -> A)
> tail f k = f (FS k)


> ||| Maps a finite function to a vector
> toVect : {A : Type} -> (Fin n -> A) -> Vect n A
> toVect {n =   Z} _ = Nil
> toVect {n = S m} f = (f FZ) :: (toVect (tail f)) 


> ||| Sum of the values of a finite function
> sum : (Fin n -> Nat) -> Nat
> sum {n = Z}   f = Z
> sum {n = S m} f = f FZ + sum (tail f)




