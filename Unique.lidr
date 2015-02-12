> module Unique -- from an idea by Tim Richter


> %default total


> Unique : Type -> Type
> Unique P = (p : P) -> (q : P) -> p = q

> Unique0 : Type -> Type
> Unique0 = Unique

> Unique1 : {t0 : Type} -> (t0 -> Type) -> Type
> Unique1 {t0} P = (a : t0) -> Unique0 (P a) 
