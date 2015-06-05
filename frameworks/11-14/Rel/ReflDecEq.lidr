> module ReflDecEq

> -- import Logic.Ops
> import Rel.DecEq


> class DecEq.DecEq alpha => ReflDecEq alpha where
>   reflexive_dec_eq : (a : alpha) ->
>                      dec_eq a a = Left {a = (a = a)} {b = (Not (a = a))} refl
