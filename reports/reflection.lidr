> import Data.Fin
> import Data.Vect
> import Control.Isomorphism


> %default total 


> Dec1 : (P : alpha -> Type) -> Type
> Dec1 {alpha} P  =  (a : alpha) -> Dec (P a) 

> Prop1 : (alpha -> Type) -> Type
> Prop1 {alpha} P = (a : alpha) -> (p : P a) -> (q : P a) -> p = q 

> Finite : Type -> Type
> Finite alpha = Exists (\ n => Iso alpha (Fin n))

> asSigmaVect : (alpha : Type) ->
>               (P : alpha -> Type) ->
>               Finite alpha -> 
>               Dec1 {alpha} P -> 
>               (n ** Vect n (Sigma alpha P))
 
> lula : (alpha : Type) -> 
>        (Q : alpha -> Type) ->
>        Finite alpha -> 
>        Dec1 {alpha} Q -> 
>        Prop1 {alpha} Q -> 
>        Finite (Sigma alpha Q)
> lula alpha Q fa dp pp with (getWitness (asSigmaVect alpha Q fa dp))
>   | (S n) = Evidence (S n) iso where
>     iso  :  Iso (a : alpha ** Q a) (Fin (S n))

> lala : (alpha : Type) -> 
>        (P : alpha -> Type) ->
>        Finite alpha -> 
>        Dec1 {alpha} P -> 
>        Prop1 {alpha} P -> 
>        Finite (Sigma alpha P)
> lala alpha P fa dp pp with (getWitness (asSigmaVect alpha P fa dp))
>   | (S n) = Evidence (S n) iso where
>     iso  :  Iso (a : alpha ** P a) (Fin (S n))


