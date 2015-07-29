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

> public plusSign1 : (q1 : Q) -> (q2 : Q) -> 
>                    Not (sign q1 = Minus) -> Not (sign q2 = Minus) ->
>                    Not (sign (plus q1 q2) = Minus)

> public multSign1 : (q1 : Q) -> (q2 : Q) -> 
>                    Not (sign q1 = Minus) -> Not (sign q2 = Minus) ->
>                    Not (sign (mult q1 q2) = Minus)



