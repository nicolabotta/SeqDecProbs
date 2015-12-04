> module PNat


> import Syntax.PreorderReasoning

> import NatPositive


> %default total


> ||| Positive natural numbers as sigma types
> PNat : Type
> PNat = Subset Nat Positive
