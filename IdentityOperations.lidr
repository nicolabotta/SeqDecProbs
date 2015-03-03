> module IdentityOperations


> import Control.Monad.Identity

> -- import ClassContainerMonad


> %default total 


|Identity| is a container monad:

> {-

> -- ||| Membership
> ClassContainerMonad.Elem {A} Identity a1 (Id {a = A} a2) = a1 = a2

> -}


> ||| Membership
> Elem : {A : Type} -> (a : A) -> (ma : Identity A) -> Type
> Elem a1 (Id a2) = a1 = a2


> ||| Tagging
> tagElem  :  {A : Type} -> (ma : Identity A) -> Identity (a : A ** a `Elem` ma)
> tagElem (Id a) = Id (a ** Refl)

