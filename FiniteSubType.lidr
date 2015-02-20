> module FiniteSubType


> import Finite
> import SubType
> import Unique


> %default total


> FiniteSubType : (A : Type) -> (P   : A -> Type) -> Unique1 P -> Type
> FiniteSubType A P uP = Finite (SubType A P uP)
