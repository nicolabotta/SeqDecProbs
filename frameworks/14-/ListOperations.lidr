> module ListOperations


> import Data.List
> import Data.List.Quantifiers

> import Sigma

> %default total

> %access public export


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

> ||| Tagging
> tagElem  :  {A : Type} -> (as : List A) -> List (Sigma A (\ a => a `Elem` as))
> tagElem Nil = Nil
> tagElem {A} (x :: xs) = (MkSigma x Here) :: (map f (tagElem xs)) where
>   f : Sigma A (\ a => a `Elem` xs) -> Sigma A (\ a => a `Elem` (x :: xs))
>   f (MkSigma a p) = MkSigma a (There p)

