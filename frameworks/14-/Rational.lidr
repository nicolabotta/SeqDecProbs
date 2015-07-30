> module Rational

> import Data.Sign

> import SignProperties
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


* Constants

> ||| Zero
> public zeroQ : Q

> public zeroQSpec : numerator zeroQ = Z


* Operations

> |||
> public fromIntegerQ : Integer -> Q

> |||
> public neg : Q -> Q

> public negSpec0 : (q : Q) -> sign q = Zero -> sign (neg q) = Zero
> public negSpec1 : (q : Q) -> sign q = Minus -> sign (neg q) = Plus
> public negSpec2 : (q : Q) -> sign q = Plus -> sign (neg q) = Minus

> |||
> public plus  : Q -> Q -> Q

> |||
> public minus : Q -> Q -> Q

> |||
> public mult  : Q -> Q -> Q


* Properties

> instance Num Q where
>   (+) = plus
>   (-) = minus
>   (*) = mult
>   
>   abs q = if (sign q == Minus) then neg q else q
>   
>   fromInteger = fromIntegerQ


> public NonNeg : Q -> Type
> NonNeg q = Not (sign q = Minus)

Patrik: TODO: Here (as in NonNegRational.lidr) it feels a bit
backwards to use |Not| when a positive formulation would be possible.

For example, with the natural ordering on Sign (TODO: define it - probably in Data.Sign in contrib).

NonNeg q = sign q > Minus

> public nonNegZeroQ : NonNeg zeroQ
> nonNegZeroQ = s2 where
>   s1 : sign zeroQ = Zero
>   s1 = signZero zeroQ zeroQSpec
>   s2 : Not (sign zeroQ = Minus)
>   s2 = replace {x = Zero} {y = sign zeroQ} {P = \ ZUZU => Not (ZUZU = Minus)} (sym s1) zeroNotMinus

> public plusSign1 : (q1 : Q) -> (q2 : Q) -> NonNeg q1 -> NonNeg q2 -> NonNeg (plus q1 q2)

> public multSign1 : (q1 : Q) -> (q2 : Q) -> NonNeg q1 -> NonNeg q2 -> NonNeg (mult q1 q2)
