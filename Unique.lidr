> module Unique -- from an idea by Tim Richter


> %default total


> Unique : Type -> Type
> Unique t = (p : t) -> (q : t) -> p = q

> Unique0 : Type -> Type
> Unique0 = Unique

> Unique1 : (t0 -> Type) -> Type
> Unique1 {t0} t1 = (v : t0) -> Unique0 (t1 v) 

> UniqueEq0 : Type -> Type
> UniqueEq0 A = (a1 : A) -> (a2 : A) -> Unique (a1 = a2) 

> UniqueEq1 : {A : Type} -> (P : A -> Type) -> Type
> UniqueEq1 {A} P = (a : A) -> UniqueEq0 (P a)

> {- Maybe implement via a type class ?

> class Unique t where
>   unique : (p : t) -> (q : t) -> p = q 
 
> -}
