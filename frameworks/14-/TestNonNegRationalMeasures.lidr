> module Main

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import NonNegRationalMeasures
> import Fraction
> import FractionPredicates
> import FractionBasicOperations
> import PNat
> import PNatOperations
> import PNatProperties
> import NatPositive

> %default total
> %auto_implicits off


> f1 : Fraction
> f1 = (1, Element (S 6) (MkPositive {n = 6})) 

> f2 : Fraction
> f2 = (1, Element (S 13) (MkPositive {n = 13})) 

> f3 : Fraction
> f3 = (1, Element (S 17) (MkPositive {n = 17})) 

> f4 : Fraction
> f4 = (2, Element (S 6) (MkPositive {n = 6})) 

> f5 : Fraction
> f5 = (3, Element (S 17) (MkPositive {n = 17})) 

> f6 : Fraction
> f6 = (1, Element (S 13) (MkPositive {n = 13})) 

> f7 : Fraction
> f7 = (2, Element (S 6) (MkPositive {n = 6}))

> zs : List NonNegRational
> zs = map fromFraction [f1,f1,f1,f1,f1,f1,f1]

> main : IO ()               
> main = do putStrLn (show (sum zs))
>           putStrLn (show (average zs))



