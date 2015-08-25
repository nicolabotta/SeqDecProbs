> module NonNegRational


> import NatPredicates


> %default total


> ||| Non negative rationals
> data NonNegQ : Type where
>   -- MkNonNegQ : (n : Nat) -> (d : Nat) -> Not (d = Z) -> Coprime n d -> NonNegQ
>   MkNonNegQ : (n : Nat) -> (d : Nat) -> Z `LT` d -> Coprime n d -> NonNegQ

> {-

> toNat : NonNegQ -> 
> toNat (MkNonNegQ q nnq) = q

> |||
> toQLemma : (q : NonNegQ) -> NonNeg (toQ q)
> toQLemma (MkNonNegQ q nnq) = nnq

> |||
> toQfromQLemma : (q : Q) -> (nnq : Not (sign q = Minus)) -> toQ (fromQ q nnq) = q
> toQfromQLemma q nnq = Refl

> ---}
