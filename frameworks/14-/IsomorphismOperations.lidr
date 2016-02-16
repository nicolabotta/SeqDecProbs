> module IsomorphismOperations

> import Data.Fin
> import Control.Isomorphism


> %default total 

> %access public export


> to : {A, B : Type} -> Iso A B -> (A -> B)
> to (MkIso to from toFrom fromTo) = to


> from : {A, B : Type} -> Iso A B -> (B -> A)
> from (MkIso to from toFrom fromTo) = from


> toFrom : {A, B : Type} -> (iso : Iso A B) -> (b : B) -> to iso (from iso b) = b
> toFrom (MkIso to from toFrom fromTo) = toFrom


> fromTo : {A, B : Type} -> (iso : Iso A B) -> (a : A) -> from iso (to iso a) = a
> fromTo (MkIso to from toFrom fromTo) = fromTo
