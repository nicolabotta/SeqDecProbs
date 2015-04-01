> import Data.Vect
> import Data.Fin
> import Data.So
> import Decidable.Order

> %default total

> class (Preorder t to) => Preordered t (to : t -> t -> Type) | t where 
>   total preorder : (a : t) -> (b : t) -> Either (to a b) (to b a)       

> instance Uninhabited (LTE (S n) Z) where
>   uninhabited LTEZero impossible
>   uninhabited (LTESucc x) impossible

> idSuccPreservesLTE : (m : Nat) -> (n : Nat) -> m `LTE` n -> m `LTE` (S n)
> idSuccPreservesLTE  Z     n    prf = LTEZero
> idSuccPreservesLTE (S m)  Z    prf = absurd prf
> idSuccPreservesLTE (S m) (S n) prf = LTESucc (idSuccPreservesLTE m n (fromLteSucc prf))

> ltZS : (m : Nat) -> LT Z (S m)
> ltZS  Z    = LTESucc LTEZero 
> ltZS (S m) = idSuccPreservesLTE (S Z) (S m) (ltZS m)

> argmaxMax : {A : Type} -> {TO : A -> A -> Type} -> Preordered A TO => 
>             Vect n A -> LT Z n -> (Fin n, A)
> argmaxMax     {n = Z}        Nil                p = absurd p
> argmaxMax     {n = S Z}     (a :: Nil)          _ = (FZ, a)
> argmaxMax {A} {n = S (S m)} (a' :: (a'' :: as)) _ with (argmaxMax (a'' :: as) (ltZS m))
>   | (k, max) with (preorder a' max)
>     | (Left  _) = (FS k, max)
>     | (Right _) = (FZ, a')

