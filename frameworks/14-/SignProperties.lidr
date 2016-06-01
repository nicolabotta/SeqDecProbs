> module SignProperties

> import Data.Sign

> %default total


> instance Eq Sign where
>   (==) Plus  Plus  = True
>   (==) Plus  Zero  = False
>   (==) Plus  Minus = False
>   (==) Zero  Plus  = False
>   (==) Zero  Zero  = True
>   (==) Zero  Minus = False
>   (==) Minus Minus = True
>   (==) Minus Zero  = False
>   (==) Minus Plus  = False

> |||
> plusNotZero : Plus = Zero -> Void
> plusNotZero Refl impossible
> %freeze plusNotZero

> |||
> plusNotMinus : Plus = Minus -> Void
> plusNotMinus Refl impossible
> %freeze plusNotMinus

> |||
> zeroNotMinus : Zero = Minus -> Void
> zeroNotMinus Refl impossible
> %freeze zeroNotMinus


> instance DecEq Sign where
>   decEq Plus Plus   = Yes Refl
>   decEq Plus Zero   = No plusNotZero
>   decEq Plus Minus  = No plusNotMinus
>   decEq Zero Plus   = No (negEqSym plusNotZero)
>   decEq Zero Zero   = Yes Refl
>   decEq Zero Minus  = No zeroNotMinus
>   decEq Minus Plus  = No (negEqSym plusNotMinus)
>   decEq Minus Zero  = No (negEqSym zeroNotMinus)
>   decEq Minus Minus = Yes Refl
