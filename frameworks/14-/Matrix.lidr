> module Matrix

> import Data.Vect

> %default total


> Matrix : (m : Nat) -> (n : Nat) -> Type -> Type
> Matrix m n t = Vect m (Vect n t)
