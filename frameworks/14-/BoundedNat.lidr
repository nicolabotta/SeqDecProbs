> module BoundedNat

> import Sigma

> %default total

> %access public export


> ||| Natural numbers bounded by LT
> LTB : Nat -> Type
> LTB b = Sigma Nat (\ n  => LT n b)

> ||| Natural numbers bounded by LTE
> LTEB : Nat -> Type
> LTEB b = Sigma Nat (\ n  => LTE n b)
