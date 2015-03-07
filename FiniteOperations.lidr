> module FiniteOperations

> import Data.Fin
> import Data.Vect
> import Data.Vect.Quantifiers
> import Control.Isomorphism

> import Finite
> import FinOperations
> import IsomorphismOperations
> import NatProperties


> %default total 


Finite types are dependent pairs: an |n : Nat| (the cardinality of the
type) and an isomorphism to |Fin n|. Here we extract the cardinality.

> ||| Cardinality of finite types
> card : {A : Type} -> (fA : Finite A) -> Nat
> card = getWitness 


Finite types are dependent pairs: an |n : Nat| (the cardinality of the
type) and an isomorphism to |Fin n|. Here we extract the isomorphism.

> ||| Isomorphism of finite types
> iso : {A : Type} -> (fA : Finite A) -> Iso A (Fin (card fA))
> iso = getProof


> {-

Finite types are dependent pairs: an |n : Nat| (the cardinality of the
type) and an isomorphism to |Fin n|. Here we extract the components of
the isomorphism.

> ||| For a finite type |A| of cardinality |n|, maps |A|-values to |Fin n|-values
> toFin : {A : Type} -> (fA : Finite A) -> (A -> Fin (card fA))
> toFin (Evidence n (MkIso to from toFrom fromTo)) = to

> ||| For a finite type |A| of cardinality |n|, maps |Fin n|-values to |A|-values
> fromFin : {A : Type} -> (fA : Finite A) -> (Fin (card fA) -> A)
> fromFin (Evidence n (MkIso to from toFrom fromTo)) = from

> ||| |toFin| is the left inverse of |fromFin|
> toFinFromFin : {A : Type} -> (fA : Finite A) -> (k : Fin (card fA)) -> toFin fA (fromFin fA k) = k
> toFinFromFin (Evidence n (MkIso to from toFrom fromTo)) = toFrom

> ||| |fromFin| is the left inverse of |toFin| 
> FromFinToFin : {A : Type} -> (fA : Finite A) -> (a : A) -> fromFin fA (toFin fA a) = a
> FromFinToFin (Evidence n (MkIso to from toFrom fromTo)) = fromTo

> -}

We can represent a finite type |A| of cardinality |n| with a vector of
elements of type |A| of length |n|. This can be done by calling
|FinOperations.toVect| on the finite function associated (via ||) to |A|.

> ||| Maps a finite type |A| of cardinality |n| to a vector of |A|-values of length |n| 
> toVect : {A : Type} -> (fA : Finite A) -> Vect (card fA) A
> toVect (Evidence n iso) = toVect (from iso)
> -- toVect fA = toVect (from (iso fA))  
> -- toVect fA = toVect (fromFin fA) 


> ||| 
> Empty : {A : Type} -> Finite A -> Type
> Empty fA = card fA = Z


> ||| 
> NonEmpty : {A : Type} -> Finite A -> Type
> NonEmpty = Not . Empty
> -- NonEmpty fA = LT Z (card fA)








