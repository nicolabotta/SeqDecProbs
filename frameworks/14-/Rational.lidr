> module Rational

> import Data.Sign

> import NatPredicates


> %default total


> %hide sign


* Specification

> data Q : Type

> |||
> public sign : Q -> Sign

> |||
> public numerator : Q -> Nat

> |||
> public denominator : Q -> Nat

> |||
> public denNotZero : (q : Q) -> Not (denominator q = Z)

> |||
> public numDenCoprime : (q : Q) -> Coprime (numerator q) (denominator q)

> |||
> public signZero : (q : Q) -> numerator q = Z -> sign q = Zero


* Operations

> |||
> public plus  : Q -> Q -> Q

> |||
> public minus : Q -> Q -> Q

> |||
> public mult  : Q -> Q -> Q


* Properties

> public NonNeg : Q -> Type
> NonNeg q = Not (sign q = Minus)

Patrik: TODO: Here (as in NonNegRational.lidr) it feels a bit
backwards to use |Not| when a positive formulation would be possible.

For example, with the natural ordering on Sign (TODO: define it - probably in Data.Sign in contrib).

NonNeg q = sign q > Minus

> public plusSign1 : (q1 : Q) -> (q2 : Q) -> NonNeg q1 -> NonNeg q2 -> NonNeg (plus q1 q2)
> public multSign1 : (q1 : Q) -> (q2 : Q) -> NonNeg q1 -> NonNeg q2 -> NonNeg (mult q1 q2)
