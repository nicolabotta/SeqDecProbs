> module VectOperations


> import Data.Vect
> import Data.Fin


> %default total


> ||| Lookup the index of an element of a vector
> lookup : {A : Type} -> (a : A) -> (as : Vect n A) -> Elem a as -> Fin n
> lookup {n = Z}   a  Nil        Here         impossible
> lookup {n = Z}   a  Nil       (There p)     impossible
> lookup {n = S m} a (a :: as)   Here       = FZ
> lookup {n = S m} a (a' :: as) (There prf) = FS (lookup a as prf)

