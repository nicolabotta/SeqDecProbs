> module Main

> import PNat
> import PNatOperations
> import PNatProperties
> import NatPositive

> %default total
> %auto_implicits off


> x : PNat
> x = fromNat 616 (LTESucc LTEZero)

> y : PNat
> y = -- Element (S 12748) (MkPositive {n = 12748})
>     fromNat (S 12748) (LTESucc LTEZero)

> main : IO ()               
> main = do putStrLn ("x = " ++ show x)
>           putStrLn ("y = " ++ show y)
>           putStrLn ("x + y = " ++ show (x + y))
>           putStrLn ("y + x = " ++ show (y + x))
>           putStrLn ("x * y = " ++ show (x * y))
>           putStrLn ("y * x = " ++ show (y * x))




