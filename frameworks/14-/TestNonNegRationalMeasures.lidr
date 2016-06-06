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
> f1 = (2067, PNatOperations.fromNat 61 (LTESucc LTEZero)) 

> f2 : Fraction
> f2 = (32, PNatOperations.fromNat 11 (LTESucc LTEZero)) 

> f3 : Fraction
> f3 = (1, PNatOperations.fromNat 19 (LTESucc LTEZero)) 

> f4 : Fraction
> f4 = (1, Element (S 12748) (MkPositive {n = 12748}))

> f5 : Fraction
> f5 = (37, PNatOperations.fromNat 15 (LTESucc LTEZero)) 

> f6 : Fraction
> f6 = (1, PNatOperations.fromNat 6 (LTESucc LTEZero)) 

> f7 : Fraction
> f7 = (1, PNatOperations.fromNat 7 (LTESucc LTEZero)) 

> zs : List NonNegRational
> zs = map fromFraction [f1,f2,f3,f4]

> main : IO ()               
> main = do putStrLn (show (sum zs))
>           putStrLn (show (average zs))



