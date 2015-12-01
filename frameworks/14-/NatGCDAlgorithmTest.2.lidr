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
> m  = 2067
> %freeze m

> x  : (Nat, PNat)
> x  = (Main.m, fromNat 616 (LTESucc LTEZero))

> y  : (Nat, PNat)
> y  = let m      : Nat
>                 = fst Main.x in 
>      let d'     : PNat
>                 = snd Main.x in 
>      let d      : Nat
>                 = toNat d' in 
>      let g      : Nat
>                 = gcdAlg m d in
>      let prf    : (GCD g m d)
>                 = gcdAlgLemma m d in
>      let gDm    : (g `Divisor` m)
>                 = gcdDivisorFst prf in
>      let gDd    : (g `Divisor` d)
>                 = gcdDivisorSnd prf in
>      let qmg    : Nat
>                 = quotient m g gDm in
>      let qdg    : Nat
>                 = quotient d g gDd in
>      let zLTd   : (Z `LT` d)
>                 = toNatLTLemma d' in 
>      let zLTqdg : (Z `LT` qdg)
>                 = quotientPreservesPositivity d g gDd zLTd in
>      (qmg, fromNat qdg zLTqdg)

> main : IO ()               
> main = do putStrLn (show y)

