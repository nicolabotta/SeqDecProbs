> module NonNegRational

> import Data.Sign

> import Rational


> %default total


* Specification

> ||| Non negative rationals
> data NonNegQ : Type where
>   MkNonNegQ : (q : Q) -> Not (sign q = Minus) -> NonNegQ

> fromQ : (q : Q) -> Not (sign q = Minus) -> NonNegQ
> fromQ = MkNonNegQ

> toQ : NonNegQ -> Q

> toQSpec : (q : NonNegQ) -> Not (sign (toQ q) = Minus)


* Operations

> plus : NonNegQ -> NonNegQ -> NonNegQ
> plus q1 q2 = fromQ q nnq where
>   q   : Q
>   q   = Rational.plus (toQ q1) (toQ q2)
>   nnq : Not (sign q = Minus) 
>   nnq = plusSign1 (toQ q1) (toQ q2) (toQSpec q1) (toQSpec q2)

> mult : NonNegQ -> NonNegQ -> NonNegQ
> mult q1 q2 = fromQ q nnq where
>   q   : Q
>   q   = Rational.mult (toQ q1) (toQ q2)
>   nnq : Not (sign q = Minus) 
>   nnq = multSign1 (toQ q1) (toQ q2) (toQSpec q1) (toQSpec q2)
