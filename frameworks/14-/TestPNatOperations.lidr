> module Main

> import PNat
> import PNatOperations
> import PNatProperties
> import NatPositive

> %default total
> %auto_implicits off


> x : PNat
> x = Element (S 615) (MkPositive {n = 615})

> y : PNat
> y = Element (S 12748) (MkPositive {n = 12748})

> main : IO ()               
> main = do putStrLn ("x = " ++ show x)
>           putStrLn ("y = " ++ show y)
>           putStrLn ("x + y = " ++ show (x + y))
>           putStrLn ("y + x = " ++ show (y + x))
>           putStrLn ("x * y = " ++ show (x * y))
>           putStrLn ("y * x = " ++ show (y * x))




