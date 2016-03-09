> module PNat

> import PNat
> import PNatOperations
> import NatPositive


> %default total
> %access public export


> ||| PNat is an instance of Show
> implementation Show PNat where
>   show = show . toNat

