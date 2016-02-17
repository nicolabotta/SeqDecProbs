> module Main

> import NatGCD
> import NatGCDOperations
> import NatGCDProperties
> import NatGCDAlgorithm
> import NatDivisor
> import NatDivisorOperations
> import NatDivisorProperties
> import PNat
> import PNatOperations
> import PNatProperties
> import NatPositive

> %default total


> m  : Nat
> m  = 42449
> %freeze m

> x  : (Nat, PNat)
> x  = (Main.m, fromNat 6776 (LTESucc LTEZero))
> %freeze x

> d'     : PNat
> d'     = snd Main.x
> d      : Nat
> d      = toNat Main.d'
> g      : Nat
> g      = gcdAlg Main.m Main.d
> prf    : (GCD Main.g Main.m Main.d)
> prf    = gcdAlgLemma Main.m Main.d
> gDm    : (Main.g `Divisor` Main.m)
> gDm    = gcdDivisorFst Main.prf
> gDd    : (Main.g `Divisor` Main.d)
> gDd    = gcdDivisorSnd Main.prf
> qmg    : Nat
> qmg    = quotient Main.m Main.g Main.gDm
> qdg    : Nat
> qdg    = quotient Main.d Main.g Main.gDd
> zLTd   : (Z `LT` Main.d)
> zLTd   = toNatLTLemma Main.d'
> zLTqdg : (Z `LT` Main.qdg)
> zLTqdg = quotientPreservesPositivity Main.d Main.g Main.gDd Main.zLTd
> y      : (Nat, PNat)
> y      = (Main.qmg, fromNat Main.qdg Main.zLTqdg)

> main : IO ()               
> main = do putStrLn (show y)

