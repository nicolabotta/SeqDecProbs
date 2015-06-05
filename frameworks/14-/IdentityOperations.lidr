> module IdentityOperations


> import Control.Monad.Identity


> %default total


|Identity| is a container monad:

> ||| Membership
> Elem : {A : Type} -> (a : A) -> (ma : Identity A) -> Type
> Elem a1 (Id a2) = a1 = a2


> ||| Tagging
> tagElem  :  {A : Type} -> (ma : Identity A) -> Identity (a : A ** a `Elem` ma)
> tagElem (Id a) = Id (a ** Refl)
