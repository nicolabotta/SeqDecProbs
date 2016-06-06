> module Main

> import Fraction
> import FractionBasicOperations
> import PNat
> import PNatOperations
> import PNatProperties

> %default total
> %auto_implicits off


> x : Fraction
> x = (2067, PNat.fromNat 616 (LTESucc LTEZero)) 

> y : Fraction
> y = (32, PNat.fromNat 11 (LTESucc LTEZero))

> z : Fraction
> z = (1, PNat.fromNat 12749 (LTESucc LTEZero))

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



