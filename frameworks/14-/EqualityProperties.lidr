> module EqualityProperties


> import Unique


> %default total


> ||| Equality is unique
> uniqueEq : {A : Type} -> (a1 : A) -> (a2 : A) -> Unique (a1 = a2)
> uniqueEq a a Refl Refl = Refl


