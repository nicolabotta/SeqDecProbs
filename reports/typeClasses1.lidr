> import Control.Monad.Identity

> namespace ContainerMonad
>   Elem : {m : Type -> Type} -> a -> m a -> Type

> ContainerMonad.Elem {m} a1 (Id a2) = a1 = a2
