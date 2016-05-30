> module Main

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import Fraction
> import FractionBasicOperations
> import PNat
> import PNatOperations
> import PNatProperties


> %default total


> z1 : NonNegRational
> z1 = fromFraction (0, PNat.fromNat 1 (LTESucc LTEZero)) 

> z2 : NonNegRational
> z2 = fromFraction (0, PNat.fromNat 7 (LTESucc LTEZero)) 

> s1 : NonNegRationalBasicOperations.num z1 = Z
> s1 = Refl

> z1EQz2 : z1 = z2
> z1EQz2 = Refl

> x : NonNegRational
> x = fromFraction (2067, PNat.fromNat 616 (LTESucc LTEZero)) 

> y : NonNegRational
> y = fromFraction (32, PNat.fromNat 11 (LTESucc LTEZero))

> z : NonNegRational
> z = x + y

> main : IO ()               
> main = do putStrLn (show z1)
>           putStrLn (show z2)
>           putStrLn (show x)
>           putStrLn (show y)
>           putStrLn (show z)


