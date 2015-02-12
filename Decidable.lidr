> module Decidable


> %default total 


> Dec0 : Type -> Type
> Dec0 = Dec

> Dec1 : {A : Type} -> (P : A -> Type) -> Type
> Dec1 {A} P = (a : A) -> Dec0 (P a) 

> DecEq0 : Type -> Type
> DecEq0 A = (a1 : A) -> (a2 : A) -> Dec (a1 = a2) 

> DecEq1 : {A : Type} -> (P : A -> Type) -> Type
> DecEq1 {A} P = (a : A) -> DecEq0 (P a)
