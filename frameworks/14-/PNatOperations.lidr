> module PNat


> import PNat
> import NatPositive
> import NatOperations
> import NatProperties


> %default total


> ||| The predecessor of a PNat
> pred : PNat -> Nat
> pred (Element _ (MkPositive {n})) = n


> ||| 
> fromNat : (m : Nat) -> Z `LT` m -> PNat
> fromNat m prf = Element m pm where
>   pm : Positive m
>   pm = fromSucc (pred m prf) m (predLemma m prf)


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

