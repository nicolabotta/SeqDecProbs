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

> %default total
> %auto_implicits off

> %freeze PNat.fromNat
> %freeze fromFraction
> %freeze sum
> %freeze average

> f1 : Fraction
> f1 = (2067, PNat.fromNat 61 (LTESucc LTEZero)) 

> f2 : Fraction
> f2 = (32, PNat.fromNat 11 (LTESucc LTEZero)) 

> f3 : Fraction
> f3 = (1, PNat.fromNat 19 (LTESucc LTEZero)) 

> f4 : Fraction
> f4 = (1, PNat.fromNat 12749 (LTESucc LTEZero)) 

> f5 : Fraction
> f5 = (37, PNat.fromNat 15 (LTESucc LTEZero)) 

> f6 : Fraction
> f6 = (1, PNat.fromNat 6 (LTESucc LTEZero)) 

> f7 : Fraction
> f7 = (1, PNat.fromNat 7 (LTESucc LTEZero)) 

> zs : List NonNegRational
> zs = map fromFraction [f1,f2,f3,f4]

> main : IO ()               
> main = do putStrLn (show (sum zs))
>           putStrLn (show (average zs))



