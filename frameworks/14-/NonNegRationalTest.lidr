> module Main

> import NonNegRational
> import NonNegRationalOperations
> import NonNegRationalProperties
> import Fraction
> import FractionOperations
> import FractionProperties
> import PNat
> import PNatOperations
> import PNatProperties
> -- import NatProperties

> %default total

> -- zLTs : {m : Nat} -> LT Z (S m)
> -- zLTs {m} = ltZS m

> x' : Fraction
> x' = (2067, PNat.fromNat 616 (LTESucc LTEZero)) 

> y' : Fraction
> y' = (32, PNat.fromNat 11 (LTESucc LTEZero))

> z' : Fraction
> z' = normalize x' -- (x' `plus` y')

> {-
> x : NonNegRational
> x = fromFraction x'

> y : NonNegRational
> y = fromFraction y'

> z : NonNegRational
> -- z = x `plus` y
> z = x + y
> -}

> main : IO ()               
> main = do putStrLn (show x')
>           putStrLn (show y')
>           putStrLn (show z')
>           -- putStrLn (show x)
>           -- putStrLn (show y)
>           -- putStrLn (show z)

