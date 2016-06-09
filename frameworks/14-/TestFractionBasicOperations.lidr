> module Main

> import Fraction
> import FractionBasicOperations
> import FractionBasicProperties
> import PNat
> import PNatOperations
> import PNatProperties
> import NatPositive

> %default total
> %auto_implicits off


> dx : PNat
> dx = Element (S 615) (MkPositive {n = 615})
> x  : Fraction
> x  = (2067, dx) 

> dy : PNat
> dy = Element (S 10) (MkPositive {n = 10})
> y  : Fraction
> y  = (32, dy)

> dz : PNat
> dz = Element (S 12748) (MkPositive {n = 12748})
> z  : Fraction
> z  = (1, dz)

> main : IO ()               
> main = do putStrLn ("x = " ++ show x)
>           putStrLn ("y = " ++ show y)
>           putStrLn ("z = " ++ show z)
>           putStrLn ("x + y = " ++ show (x + y))
>           putStrLn ("y + x = " ++ show (y + x))
>           putStrLn ("x * y = " ++ show (x * y))
>           putStrLn ("y * x = " ++ show (y * x))
>           putStrLn ("(x + y) + z = " ++ show ((x + y) + z))
>           putStrLn ("x + (y + z) = " ++ show (x + (y + z)))
>           putStrLn ("(x * y) * z = " ++ show ((x * y) * z))
>           putStrLn ("x * (y * z) = " ++ show (x * (y * z)))



