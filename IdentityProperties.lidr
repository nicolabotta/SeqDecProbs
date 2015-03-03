> module IdentityProperties


> import Control.Monad.Identity

> import IdentityOperations
> import Decidable


> %default total 


Container monad decidability:

> ||| |Elem| is decidable
> decElem : {A : Type} -> DecEq0 A -> (a : A) -> (ma : Identity A) -> Dec (a `Elem` ma)
> decElem dec a1 (Id a2) with (dec a1 a2)
>   | (Yes prf)   = Yes prf
>   | (No contra) = No contra    


