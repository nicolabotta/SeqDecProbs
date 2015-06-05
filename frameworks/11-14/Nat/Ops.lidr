> module Ops

> toFloatNat : Nat -> Float
> toFloatNat Z = 0.0
> toFloatNat (S k) = 1.0 + toFloatNat k   

> instance Cast Nat Float where
>   cast = toFloatNat  