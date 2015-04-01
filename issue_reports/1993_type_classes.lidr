> import Control.Monad.Identity
> %default total 

> class Monad m => ContainerMonad (m : Type -> Type) where
>   Elem    : a -> m a -> Type
>   ret     : a -> m a
>   ret     = pure
>   spec1   : {x : a} -> Elem {a = a} x (ret {a = a} x)

> instance ContainerMonad Identity where
>   Elem a1 (Id a2) = a1 = a2
>   spec1 = Refl
