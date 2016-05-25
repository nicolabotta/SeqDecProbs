> module NatPositive

> import Syntax.PreorderReasoning

> import Unique
> import SubsetProperties


> %default total
> %access public export
> %auto_implicits on


> |||
> data Positive : Nat -> Type where
>   MkPositive  : {n : Nat} -> Positive (S n)

> |||
> PositiveUnique : {n : Nat} -> Unique (Positive n)
> PositiveUnique MkPositive MkPositive = Refl

> |||
> fromSucc : (m : Nat) -> (n : Nat) -> S m = n -> Positive n
> fromSucc m n prf = s2 where
>   s1 : Positive (S m)
>   s1 = MkPositive
>   s2 : Positive n
>   s2 = replace prf s1

> |||
> implementation Uninhabited (Positive Z) where
>   uninhabited (MkPositive {n}) impossible

> |||
> positiveNotZ : {n : Nat} -> Positive n -> Not (n = Z)
> positiveNotZ {n = Z}   p = absurd p
> positiveNotZ {n = S m} _ = SIsNotZ

> |||
> plusPreservesPositivity : Positive m -> Positive n -> Positive (m + n)
> plusPreservesPositivity {m = Z  } {n      } MkPositive _            impossible
> plusPreservesPositivity {m      } {n = Z  } _          MkPositive   impossible
> plusPreservesPositivity {m = S m} {n = S n} _          _          = MkPositive

> |||
> multPreservesPositivity : Positive m -> Positive n -> Positive (m * n)
> multPreservesPositivity {m = Z  } {n      } MkPositive _            impossible
> multPreservesPositivity {m      } {n = Z  } _          MkPositive   impossible
> multPreservesPositivity {m = S m} {n = S n} _          _          = MkPositive  


