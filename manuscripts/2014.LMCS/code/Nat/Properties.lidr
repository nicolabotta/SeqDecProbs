> module Properties

> import Data.So

> import Logic.Properties

> %default total

> -- Zero is not a successor
> ZnotS : Z = S n -> Void
> ZnotS Refl impossible

> -- A successor is not zero
> SnotZ : S n = Z -> Void
> SnotZ Refl impossible

> ltZ_bot : So (n < Z) -> Void
> ltZ_bot {n = Z}   nltZ  =  soFalseElim nltZ
> ltZ_bot {n = S m} nltZ  =  soFalseElim nltZ

