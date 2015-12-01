> module Main
> import NonNegRational2
> import PNatOperations


> %default total

> x : NonNegRational
> x = fromFraction (25, PNat.fromNat 56 (LTESucc LTEZero))
> y : NonNegRational
> y = fromFraction (32, PNat.fromNat 11 (LTESucc LTEZero))
> z : NonNegRational
> z = x + y

> main : IO ()               
> main = putStrLn $ show z

