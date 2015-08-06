> module Num

> import Data.Vect

> import Matrix

> %default total


> ||| Scalar-vector "multiplication"
> multSV : (Num t) => t -> Vect m t -> Vect m t
> -- multSV _ Nil = Nil
> -- multSV x (y :: ys) = (x * y) :: (multSV x ys)
> multSV x = map (x *)


> ||| Vector-matrix "multiplication" (kind of)
> multVM : (Num t) => Vect m t -> Matrix m n t -> Matrix m n t
> -- multVM {m = Z}   {n} Nil Nil = Nil
> -- multVM {m = S l} {n} (x :: xs) (v :: vs) = (multSV x v) :: (multVM xs vs)
> multVM {m} {n} xs xss = map (uncurry multSV) (zip xs xss)


> |||
> multConcat : (Num t) => Vect m t -> Vect m (Vect n t) -> Vect (m * n) t
> multConcat {m = Z}   {n} Nil Nil = Nil
> multConcat {m = S l} {n} (x :: xs) (v :: vs) = (multSV x v) ++ multConcat xs vs
