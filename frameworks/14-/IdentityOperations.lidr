> module IdentityOperations


> import Control.Monad.Identity


> import Sigma


> %default total
> %access public export
> %auto_implicits on


> |||
> unwrap : Identity a -> a
> unwrap {a} (Id x) = x


Identity is a container monad:

> ||| Membership
> Elem : {A : Type} -> A -> Identity A -> Type
> Elem a1 (Id a2) = a1 = a2

> ||| Emptiness
> Empty : {A : Type} -> Identity A -> Type
> Empty (Id a2) = Void

> ||| Non emptiness
> NonEmpty : {A : Type} -> Identity A -> Type
> NonEmpty _ = Unit

> ||| 
> All : {A : Type} -> (P : A -> Type) -> Identity A -> Type
> All P = P . unwrap

> ||| Tagging
> tagElem  :  {A : Type} -> (ia : Identity A) -> Identity (Sigma A (\ a => a `Elem` ia))
> tagElem (Id a) = Id (MkSigma a Refl)


> |||
> unwrapElemLemma : (ia : Identity a) -> Elem (unwrap ia) ia
> unwrapElemLemma (Id a) = Refl
