> module MatrixOperations

> import Data.Fin
> import Data.Vect

> import Matrix

> %default total
> %access public export


> row : (Fin m) -> Matrix m n t -> Vect n t
> row k xss = index k xss


> toVect : Matrix m n t -> Vect (m * n) t
> toVect = concat
