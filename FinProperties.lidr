> module FinProperties

> import Data.Fin
> import Data.Vect

> import FinOperations
 

> %default total

> ||| |finToNat (k : Fin n)| is LT bounded by |n| 
> finToNatLemma : (k : Fin n) -> LT (finToNat k) n 
> finToNatLemma {n = Z}   k       =  absurd k
> finToNatLemma {n = S m} FZ      =  LTESucc LTEZero 
> finToNatLemma {n = S m} (FS k)  =  LTESucc (finToNatLemma k) 


> ||| |toVect| representations of finite functions are complete
> toVectComplete : {A : Type} -> (f : Fin n -> A) -> (k : Fin n) -> Elem (f k) (toVect f)
> toVectComplete {n = Z} _  k     = void (uninhabited k)
> toVectComplete         f  FZ    = Here
> toVectComplete         f (FS j) = There (toVectComplete (tail f) j)
