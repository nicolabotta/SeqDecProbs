> module NonNegRational

> import Data.Sign

> import RationalSpecification
> import RationalProperties
> import SignedPredicates


> %default total


> ||| Non negative rationals
> data NonNegQ : Type where
>   MkNonNegQ : (q : Q) -> NonNeg q -> NonNegQ

> |||
> fromQ : (q : Q) -> Not (sign q = Minus) -> NonNegQ
> fromQ = MkNonNegQ

> |||
> toQ : NonNegQ -> Q
> toQ (MkNonNegQ q nnq) = q

> |||
> toQLemma : (q : NonNegQ) -> NonNeg (toQ q)
> toQLemma (MkNonNegQ q nnq) = nnq

> |||
> toQfromQLemma : (q : Q) -> (nnq : Not (sign q = Minus)) -> toQ (fromQ q nnq) = q
> toQfromQLemma q nnq = Refl


