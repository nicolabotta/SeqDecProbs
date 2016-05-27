> module Main

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalProperties
> import Fraction
> import FractionOperations
> import PNat
> import PNatOperations
> import PNatProperties


> %default total


> x : NonNegRational
> x = fromFraction (2067, PNat.fromNat 616 (LTESucc LTEZero)) 

> y : NonNegRational
> y = fromFraction (32, PNat.fromNat 11 (LTESucc LTEZero))

> z : NonNegRational
> z = x + y

> main : IO ()               
> main = do putStrLn (show x)
>           putStrLn (show y)
>           putStrLn (show z)


