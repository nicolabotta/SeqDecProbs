> module Main

> import NonNegRational
> import NonNegRationalMeasures
> import Fraction
> import FractionPredicates
> import FractionBasicOperations
> import PNat
> import PNatOperations
> import PNatProperties


> %default total
> %auto_implicits off


> f1 : Fraction
> f1 = (1, PNat.fromNat 1 (LTESucc LTEZero)) 

> f2 : Fraction
> f2 = (1, PNat.fromNat 2 (LTESucc LTEZero)) 

> f3 : Fraction
> f3 = (1, PNat.fromNat 3 (LTESucc LTEZero)) 

> f4 : Fraction
> f4 = (1, PNat.fromNat 4 (LTESucc LTEZero)) 

> f5 : Fraction
> f5 = (1, PNat.fromNat 5 (LTESucc LTEZero)) 

> f6 : Fraction
> f6 = (1, PNat.fromNat 6 (LTESucc LTEZero)) 

> f7 : Fraction
> f7 = (1, PNat.fromNat 7 (LTESucc LTEZero)) 

> zs : List NonNegRational
> zs = map fromFraction [f1,f2,f3,f4,f5,f6,f7]

> main : IO ()               
> main = do putStrLn (sum zs)
>           putStrLn (average zs)



