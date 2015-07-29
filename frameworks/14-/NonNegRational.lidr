> module NonNegRational

> import Data.Sign

> import Rational


> %default total


* Specification

> ||| Non negative rationals
> data NonNegQ : Type where
>   MkNonNegQ : (q : Q) -> NonNeg q -> NonNegQ

Patrik: TODO: I have a feeling that using |Not| is overkill for finite
types like |Sign|. Note that the definition (|Not a = a -> Void|) uses
a function space so each element of |NonNegQ| will (at least
conceptually) contain a function.

> fromQ : (q : Q) -> Not (sign q = Minus) -> NonNegQ
> fromQ = MkNonNegQ

> toQ : NonNegQ -> Q

> toQSpec : (q : NonNegQ) -> NonNeg (toQ q)


* Operations

> plus : NonNegQ -> NonNegQ -> NonNegQ
> plus q1 q2 = fromQ q nnq where
>   q   : Q
>   q   = Rational.plus (toQ q1) (toQ q2)
>   nnq : NonNeg q
>   nnq = plusSign1 (toQ q1) (toQ q2) (toQSpec q1) (toQSpec q2)

> mult : NonNegQ -> NonNegQ -> NonNegQ
> mult q1 q2 = fromQ q nnq where
>   q   : Q
>   q   = Rational.mult (toQ q1) (toQ q2)
>   nnq : NonNeg q
>   nnq = multSign1 (toQ q1) (toQ q2) (toQSpec q1) (toQSpec q2)

These operations
