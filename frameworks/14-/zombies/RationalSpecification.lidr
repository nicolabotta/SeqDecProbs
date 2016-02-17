> module RationalSpecification

> import Data.Sign

> import SignProperties
> import NatPredicates


> %default total
> %hide sign


> data Q : Type

> |||
> public fromIntegerQ : Integer -> Q

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


