> module Opt


> import Control.Isomorphism
> import Data.Fin
> -- import Decidable.Order

> import Finite
> import FiniteOperations
> import Order
> import OrderOperations
> import OrderProperties
> import VectOperations
> import VectProperties


> %default total 


> argmaxMax : {A, B : Type} -> {TO : B -> B -> Type} -> 
>             Preordered B TO => 
>             (fA : Finite A) -> (ne : NonEmpty fA) -> 
>             (f : A -> B) -> (A,B)
> argmaxMax {A} {B} {TO} fA prf f = VectOperations.max {A = (A,B)} {TO = sndType TO} abs where
>   abs : Vect (card fA) (A,B)
>   abs = map (\ a => (a, f a)) (toVect fA)

