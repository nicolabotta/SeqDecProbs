> module PNat


> import PNat


> %default total


> |||
> nat : PNat -> Nat
> nat = getWitness

> |||
> plus : PNat -> PNat -> PNat
> plus (Element m pm) (Element n pn) = Element (m + n) (plusPreservesIsSucc pm pn)

> |||
> (+) : PNat -> PNat -> PNat
> (+) = plus

> |||
> mult : PNat -> PNat -> PNat
> mult (Element m pm) (Element n pn) = Element (m * n) (multPreservesIsSucc pm pn)

> |||
> (*) : PNat -> PNat -> PNat
> (*) = mult

