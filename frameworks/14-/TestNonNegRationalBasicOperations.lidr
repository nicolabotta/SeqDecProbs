> module Main

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import Fraction
> import FractionPredicates
> import FractionBasicOperations
> import PNat
> import PNatOperations
> import PNatProperties
> import NatPositive

> %default total
> %auto_implicits off


> dx : PNat
> dx = Element (S 615) (MkPositive {n = 615})
> x  : NonNegRational
> x  = fromFraction (2067, dx) 

> dy : PNat
> dy = Element (S 10) (MkPositive {n = 10})
> y  : NonNegRational
> y  = fromFraction (32, dy)

> dz : PNat
> dz = Element (S 12748) (MkPositive {n = 12748})
> z  : NonNegRational
> z  = fromFraction (1, dz)

> dz1 : PNat
> dz1 = Element (S 7) (MkPositive {n = 7})
> f1  : Fraction
> f1  = (1, dz1)
> z1  : NonNegRational
> z1  = fromFraction f1

> dz2 : PNat
> dz2 = Element (S 23) (MkPositive {n = 23})
> f2  : Fraction
> f2  = (3, dz2)
> z2  : NonNegRational
> z2  = fromFraction f2

> f1Eqf2 : f1 `Eq` f2
> f1Eqf2 = Refl

> -- %freeze fromFraction

> z1EQz2 : z1 = z2
> z1EQz2 = fromFractionEqLemma f1 f2 f1Eqf2

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



