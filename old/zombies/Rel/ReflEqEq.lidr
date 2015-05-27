> module ReflEqEq

> import Logic.Properties
> import Rel.EqEq


> class EqEq alpha => ReflEqEq alpha where
>   reflexive_eqeq : (a : alpha) -> so (a == a)
>   Reflexive_eqeq : (a : alpha) -> (a == a) = True
>   Reflexive_eqeq a = soElim C refl (a == a) (reflexive_eqeq a) where
>     C : (b : Bool) -> so b -> Type
>     C b s = b = True
