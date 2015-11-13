> module PNat

> import Syntax.PreorderReasoning

> import Unique
> import SubsetProperties


> %default total


> |||
> data IsSucc : Nat -> Type where
>   MkIsSucc  : {n : Nat} -> IsSucc (S n)

> |||
> IsSuccUnique : {n : Nat} -> Unique (IsSucc n)
> IsSuccUnique MkIsSucc MkIsSucc = Refl

> |||
> fromSucc : (m : Nat) -> (n : Nat) -> S m = n -> IsSucc n
> fromSucc m n prf = s2 where
>   s1 : IsSucc (S m)
>   s1 = MkIsSucc
>   s2 : IsSucc n
>   s2 = replace prf s1

> |||
> plusPreservesIsSucc : IsSucc m -> IsSucc n -> IsSucc (m + n)
> plusPreservesIsSucc {m = Z  } {n      } MkIsSucc _        impossible
> plusPreservesIsSucc {m      } {n = Z  } _        MkIsSucc impossible
> plusPreservesIsSucc {m = S m} {n = S n} _        _        = MkIsSucc

> |||
> multPreservesIsSucc : IsSucc m -> IsSucc n -> IsSucc (m * n)
> multPreservesIsSucc {m = Z  } {n      } MkIsSucc _        impossible
> multPreservesIsSucc {m      } {n = Z  } _        MkIsSucc impossible
> multPreservesIsSucc {m = S m} {n = S n} _        _        = MkIsSucc


> ||| Positive natural numbers as sigma types 
> PNat : Type
> PNat = Subset Nat IsSucc

