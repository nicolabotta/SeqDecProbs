> module Nat


> %default total

> %hide Nat
> %hide Z
> %hide S

> namespace lala

>   data Nat : Type where
>     Z : Nat
>     S : Nat -> Nat
