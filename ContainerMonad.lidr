> module ContainerMonad


> import Control.Monad.Identity


> %default total 


> class Monad m => ContainerMonad (m : Type -> Type) where

>   Elem    : a -> m a -> Type

>   tagElem : (mx : m a) -> m (x : a ** Elem {a = a} x mx)

>   All     : (a -> Type) -> m a -> Type

>   ret     : a -> m a
>   ret     = pure

>   join    : m (m a) -> m a
>   join mma = (>>=) mma id

>   spec1   : {x : a} -> 
>             Elem {a = a} x (ret {a = a} x)

>   spec2   : {x : a} -> {mx : m a} -> {mmx : m (m a)} -> 
>             Elem {a = a} x mx -> 
>             Elem {a = m a} mx mmx -> 
>             Elem {a = a} x (join {a = a} mmx)

>   spec3   : {mx : m a} -> map getWitness (tagElem {a = a} mx) = mx

>   spec4   : {x : a} -> {mx : m a} -> {P : a -> Type} -> 
>             All {a = a} P mx -> Elem {a = a} x mx -> P x


> instance ContainerMonad Identity where
>   Elem a1 (Id a2) = a1 = a2
>   tagElem (Id a) = Id (a ** Refl)
>   All P (Id a) = P a
>   spec1 = s3 where
>     s3 : {x : a} -> Elem {a = a} x (ret {a = a} x)
>     s3 = ?liki
