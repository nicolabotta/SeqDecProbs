> module Main

> import Fraction
> import FractionOperations
> import FractionProperties
> import PNat
> import PNatOperations
> import PNatProperties

> %default total

> x : Fraction
> x = (2067, fromNat 616 (LTESucc LTEZero)) 
> %freeze x

> y : Fraction
> y = normalize x

> main : IO ()               
> main = do putStrLn (show y)

