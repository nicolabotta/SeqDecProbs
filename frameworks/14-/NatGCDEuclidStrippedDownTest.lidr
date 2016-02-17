> module Main

> import NatGCDEuclidStrippedDown

> %default total


> m : Nat
> n : Nat

> d : Nat
> d = euclidGCD m n

> m = 42449
> n = 6776

> main : IO ()               
> main = do putStrLn (show d)

