> module PNat

> import PNat
> import PNatOperations
> import NatPositive


> %default total


> ||| PNat is an instance of Show
> instance Show PNat where
>   show = show . toNat

