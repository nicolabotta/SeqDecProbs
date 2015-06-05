> module ClassContainerMonad


> %default total 


> record ContainerMonad : Type where
>   MkContainerMonad : (M    : Type -> Type) ->
>                      (Elem : {A : Type} -> A -> M A -> Type) ->
>                      ContainerMonad

> {-

>   tagElem : (ma : M A) -> M (a : A ** Elem a ma)

>   All      :  (P : A -> Type) -> M A -> Type
>   All {A} P ma = (a : A) -> a `Elem` ma -> P a

> -}
