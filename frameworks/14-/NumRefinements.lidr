> module NumRefinements


> %default total


> |||
> class (Num t) => NumPlusZeroNeutral t where
>   plusZeroLeftNeutral  : (x : t) -> 0 + x = x
>   plusZeroRightNeutral : (x : t) -> x + 0 = x


> |||
> class (NumPlusZeroNeutral t) => NumPlusAssociative t where
>   plusAssociative : (x, y, z : t) -> x + (y + z) = (x + y) + z


This should not depend on the anything more than Num, bu Idris
currently (2015-08-08) seems to have problems when combining two
classes constraining the same type so this is a temporary work-around.

class (Num t) => NumMultZeroPlus t where

> |||
> class (NumPlusAssociative t) => NumMultZeroOne t where
>   multZeroRightZero   : (x : t) -> x * 0 = 0
>   multZeroLeftZero    : (x : t) -> 0 * x = 0
>   multOneRightNeutral : (x : t) -> x * 1 = x
>   multOneLeftNeutral  : (x : t) -> 1 * x = x


> |||
> class (NumMultZeroOne t) => NumMultDistributesOverPlus t where
>   multDistributesOverPlusRight : (x, y, z : t) -> x * (y + z) = (x * y) + (x * z)
>   multDistributesOverPlusLeft  : (x, y, z : t) -> (x + y) * z = (x * z) + (y * z)
