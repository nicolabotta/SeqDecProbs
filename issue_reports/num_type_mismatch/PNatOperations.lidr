> module PNat


> import PNat
> import NatPositive


> %default total
> %access public export


> |||
> toNat : PNat -> Nat
> toNat = getWitness


> |||
> plus : PNat -> PNat -> PNat
> plus (Element m pm) (Element n pn) = Element (m + n) (plusPreservesPositivity pm pn)


> |||
> (+) : PNat -> PNat -> PNat
> (+) = plus


> |||
> mult : PNat -> PNat -> PNat
> mult (Element m pm) (Element n pn) = Element (m * n) (multPreservesPositivity pm pn)


> |||
> (*) : PNat -> PNat -> PNat
> (*) = mult

