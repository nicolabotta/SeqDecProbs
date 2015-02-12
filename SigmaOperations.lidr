> module SigmaOperations


> import Data.Fin
> import Data.Vect
> import Control.Isomorphism

> import Finite
> import Decidable
> import Unique
> import FiniteOperations
> import VectOperations


> %default total


> ||| Maps a finite type |A| and a decidable predicate |P| to a vector |Sigma A P| values
> toVect : {A : Type} ->
>          {P : A -> Type} ->
>          Finite A -> 
>          Dec1 P -> 
>          (n : Nat ** Vect n (Sigma A P))
> toVect fA d1P = filterTag d1P (toVect fA)


