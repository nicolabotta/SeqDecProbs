> module IdentityOperations


> import Control.Monad.Identity


> import Sigma


> %default total

> %access public export


> |||
> unwrap : Identity a -> a
> unwrap {a} (Id x) = x


|Identity| is a container monad:

> ||| Membership
> Elem : {A : Type} -> (a : A) -> (ma : Identity A) -> Type
> Elem a1 (Id a2) = a1 = a2


> ||| Tagging
> tagElem  :  {A : Type} -> (ma : Identity A) -> Identity (Sigma A (\ a => a `Elem` ma))
> tagElem (Id a) = Id (MkSigma a Refl)


> |||
> unwrapElemLemma : (ma : Identity a) -> Elem (unwrap ma) ma
> unwrapElemLemma (Id a) = Refl
