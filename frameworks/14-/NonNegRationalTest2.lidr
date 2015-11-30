> module Main
> import NonNegRational2
> import PNatOperations


> %default total

> x : NonNegRational
> x = fromFraction (7, PNat.fromNat 3 (LTESucc LTEZero))
> y : NonNegRational
> y = fromFraction (28, PNat.fromNat 8 (LTESucc LTEZero))
> z : NonNegRational
> z = x + y

> main : IO ()               
> main = putStrLn $ show z

