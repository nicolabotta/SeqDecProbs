> module ContainerMonad


> import Control.Monad.Identity


> %default total


> class Monad m => ContainerMonad (m : Type -> Type) where

    Requirements:

>   Elem    : a -> m a -> Type
>   tagElem : (mx : m a) -> m (x : a ** Elem {a = a} x mx)
>   All     : (a -> Type) -> m a -> Type

    Defaults:

>   ret     : a -> m a
>   ret     = pure
>   join    : m (m a) -> m a
>   join mma = (>>=) mma id

    Specifications:

> {- TODO: "Can't resolve type class ContainerMonad m"
>   spec1   : {a : Type} ->
>             {x : a} ->
>             Elem {a = a} x (ret {a = a} x)
>   spec2   : {x : a} -> {mx : m a} -> {mmx : m (m a)} ->
>             Elem {a = a} x mx ->
>             Elem {a = m a} mx mmx ->
>             Elem {a = a} x (join {a = a} mmx)
>   spec3   : {mx : m a} -> map getWitness (tagElem {a = a} mx) = mx
>   spec4   : {x : a} -> {mx : m a} -> {P : a -> Type} ->
>             All {a = a} P mx -> Elem {a = a} x mx -> P x
> -}
