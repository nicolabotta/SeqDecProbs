> module ReflEqEq

> import Data.So

> import Logic.Properties
> import Rel.EqEq


> class EqEq alpha => ReflEqEq alpha where
>   reflexive_eqeq : (a : alpha) -> So (a == a)
>   Reflexive_eqeq : (a : alpha) -> (a == a) = True
>   Reflexive_eqeq a = soElim C Refl (a == a) (reflexive_eqeq a) where
>     C : (b : Bool) -> So b -> Type
>     C b s = b = True
