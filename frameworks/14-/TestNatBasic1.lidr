> module Main

> %default total
> %auto_implicits off


> x : Nat
> x = 1

> y : Nat
> y = 2

> z : Nat
> z = 2

> yEQz : y = z
> yEQz = Refl

> xs : List Nat
> xs = [x, y, z]

> sxs : sum xs = 5
> sxs = Refl

> main : IO ()
> main = do putStrLn ("x           = " ++ show x)
>           putStrLn ("y           = " ++ show y)
>           putStrLn ("z           = " ++ show z)
>           putStrLn ("x + y       = " ++ show (x + y))
>           putStrLn ("y + x       = " ++ show (y + x))
>           putStrLn ("x * y       = " ++ show (x * y))
>           putStrLn ("y * x       = " ++ show (y * x))
>           putStrLn ("(x + y) + z = " ++ show ((x + y) + z))
>           putStrLn ("x + (y + z) = " ++ show (x + (y + z)))
>           putStrLn ("(x * y) * z = " ++ show ((x * y) * z))
>           putStrLn ("xs          = " ++ show xs)
>           putStrLn ("sum xs      = " ++ show (sum xs))



