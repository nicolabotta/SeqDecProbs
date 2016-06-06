> module NatBasicProperties

> %default total
> %auto_implicits on
> %access export
> -- %access public export


> implementation Uninhabited (S n = Z) where
>   uninhabited Refl impossible


> |||
> predInjective : (left : Nat) -> (right : Nat) -> Not (S left = S right) -> Not (left = right)
> predInjective left right contra = contra . (eqSucc left right)
> %freeze predInjective


> |||
> succInjective' : (left : Nat) -> (right : Nat) -> Not (left = right) -> Not (S left = S right)
> succInjective' left right contra = contra . (succInjective left right)
> %freeze succInjective'


> {-

> ---}
