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
> y = (32, fromNat 11 (LTESucc LTEZero)) 
> %freeze x

> z : Fraction
> z = x + y

> main : IO ()               
> main = do putStrLn ("x = " ++ show x)
>           putStrLn ("y = " ++ show y)
>           putStrLn ("z = " ++ show z)
>           putStrLn ("z = " ++ show (normalize z))

