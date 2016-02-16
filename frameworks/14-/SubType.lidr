> module SubType


> import Unique
> import Sigma


> %default total

> %access public export


> ||| For a type |A| and a unique predicate |P|, a subtype of |A| is just a set of values of |A| that fulfills |P|
> SubType : (A : Type) -> (P   : A -> Type) -> Unique1 P -> Type
> SubType A P _ = Sigma A P
