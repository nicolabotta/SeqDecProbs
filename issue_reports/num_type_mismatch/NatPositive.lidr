> module NatPositive


> %default total


> data Positive : Nat -> Type where
>   MkPositive  : {n : Nat} -> Positive (S n)


> plusPreservesPositivity : Positive m -> Positive n -> Positive (m + n)
> plusPreservesPositivity {m = Z  } {n      } MkPositive _            impossible
> plusPreservesPositivity {m      } {n = Z  } _          MkPositive   impossible
> plusPreservesPositivity {m = S m} {n = S n} _          _          = MkPositive


> multPreservesPositivity : Positive m -> Positive n -> Positive (m * n)
> multPreservesPositivity {m = Z  } {n      } MkPositive _            impossible
> multPreservesPositivity {m      } {n = Z  } _          MkPositive   impossible
> multPreservesPositivity {m = S m} {n = S n} _          _          = MkPositive  


