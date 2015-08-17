> module SignedPredicates

> import Data.Sign


> %default total


> NonNeg : (Signed t) => t -> Type
> NonNeg x = Not (sign x = Minus)

Patrik: TODO: Here it feels a bit backwards to use |Not| when a positive
formulation would be possible. For example, with the natural ordering on
Sign (TODO: define it - probably in Data.Sign in contrib).

NonNeg q = sign q > Minus



