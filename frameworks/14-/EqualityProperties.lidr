> module EqualityProperties


> import Unique


> %default total

> %access public export


> ||| Equality is unique
> uniqueEq : {A : Type} -> (a1 : A) -> (a2 : A) -> Unique (a1 = a2)
> uniqueEq a a Refl Refl = Refl
> %freeze uniqueEq -- frozen

