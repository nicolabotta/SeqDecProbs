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
> import NatProperties


> %default total


> zLTs : {m : Nat} -> LT Z (S m)
> zLTs {m} = ltZS m


> x : NonNegRational
> x = fromFraction (7, fromNat 3 zLTs) 

> y : NonNegRational
> y = fromFraction (28, fromNat 8 zLTs)


> z : NonNegRational
> z = x `plus` y


> main : IO ()               
> main = putStrLn $ show z
