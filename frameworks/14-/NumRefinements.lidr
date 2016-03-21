> module NumRefinements


> %default total

> %access public export


> |||
> interface (Num t) => NumPlusZeroNeutral t where
>   plusZeroLeftNeutral  : (x : t) -> 0 + x = x
>   plusZeroRightNeutral : (x : t) -> x + 0 = x


> |||
> -- interface (NumPlusZeroNeutral t) => NumPlusAssociative t where
> interface (Num t) => NumPlusAssociative t where
>   plusAssociative : (x, y, z : t) -> x + (y + z) = (x + y) + z


> |||
> -- interface (NumPlusAssociative t) => NumMultZeroOne t where
> interface (Num t) => NumMultZeroOne t where
>   multZeroRightZero   : (x : t) -> x * 0 = 0
>   multZeroLeftZero    : (x : t) -> 0 * x = 0
>   multOneRightNeutral : (x : t) -> x * 1 = x
>   multOneLeftNeutral  : (x : t) -> 1 * x = x


> |||
> -- interface (NumMultZeroOne t) => NumMultDistributesOverPlus t where
> interface (Num t) => NumMultDistributesOverPlus t where
>   multDistributesOverPlusRight : (x, y, z : t) -> x * (y + z) = (x * y) + (x * z)
>   multDistributesOverPlusLeft  : (x, y, z : t) -> (x + y) * z = (x * z) + (y * z)
