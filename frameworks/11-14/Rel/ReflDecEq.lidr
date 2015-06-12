> module ReflDecEq

> import Rel.DecEq


> %default total


> class DecEq.DecEq alpha => ReflDecEq alpha where
>   reflexive_dec_eq : (a : alpha) -> dec_eq a a = Left Refl
