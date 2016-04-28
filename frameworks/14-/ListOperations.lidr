> module ListOperations


> import Data.List
> import Data.List.Quantifiers

> import Sigma

> %default total
> %access public export
> %auto_implicits on


|List| is a functor:

> ||| fmap
> fmap : {A, B : Type} -> (A -> B) -> List A -> List B
> fmap = map


|List| is a monad:

> ||| ret
> ret : {A : Type} -> A -> List A
> ret = pure

> ||| bind
> bind : {A, B : Type} -> List A -> (A -> List B) -> List B
> bind = (>>=)


|List| is a container monad:

> ||| 
> Empty    : {A : Type} -> List A -> Type
> Empty  Nil      = Unit
> Empty (a :: as) = Void

> ||| Tagging
> tagElem  :  {A : Type} -> (as : List A) -> List (Sigma A (\ a => a `Elem` as))
> tagElem Nil = Nil
> tagElem {A} (x :: xs) = (MkSigma x Here) :: (map f (tagElem xs)) where
>   f : Sigma A (\ a => a `Elem` xs) -> Sigma A (\ a => a `Elem` (x :: xs))
>   f (MkSigma a p) = MkSigma a (There p)


Show

> implementation Show (Elem a as) where
>   show = show' where
>     show' : {A : Type} -> {a : A} -> {as : List A} -> Elem a as -> String 
>     show'  Here     = "Here"
>     show' (There p) = "There" ++ show' p


Reduction operators

> -- maxList : {A : Type} -> TotalPreorder A -> (as : List A) -> nonEmpty as -> A
