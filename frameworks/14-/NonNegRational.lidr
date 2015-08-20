> module NonNegRational


> import NatPredicates


> %default total


> ||| Non negative rationals
> data NonNegQ : Type where
>   MkNonNegQ : (n : Nat) -> (d : Nat) -> Not (d = Z) -> Coprime n d -> NonNegQ

> {-

> |||
> fromNat : (n : Nat) -> NonNegQ
> fromNat = MkNonNegQ n (S Z) SIsNotZ anyCoprimeOne

> toNat : NonNegQ -> 
> toNat (MkNonNegQ q nnq) = q

> |||
> toQLemma : (q : NonNegQ) -> NonNeg (toQ q)
> toQLemma (MkNonNegQ q nnq) = nnq

> |||
> toQfromQLemma : (q : Q) -> (nnq : Not (sign q = Minus)) -> toQ (fromQ q nnq) = q
> toQfromQLemma q nnq = Refl

> ---}
