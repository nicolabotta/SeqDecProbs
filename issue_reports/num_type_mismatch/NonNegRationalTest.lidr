> module Main

> import NonNegRational
> import NonNegRationalOperations
> import NonNegRationalProperties
> import Fraction
> import FractionOperations
> import PNat
> import PNatOperations
> import PNatProperties
> import NatPositive


> %default total


> x : NonNegRational
> x = fromFraction (2067, Element 616 MkPositive) 

> y : NonNegRational
> y = fromFraction (32, Element 11 MkPositive)

> z : NonNegRational
> -- z = x `plus` y
> z = x + y

> main : IO ()               
> main = do putStrLn (show z)


