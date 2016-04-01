> module IdentityProperties


> import Control.Monad.Identity

> import IdentityOperations
> -- import ContainerMonad
> import Decidable
> import Unique


> %default total

> %access public export


> ||| Id is injective
> injectiveId : {a : Type} -> {left : a} -> {right : a} -> (Id left) = (Id right) -> left = right
> injectiveId Refl = Refl

> {-

> ||| Identity is a container monad
> instance ContainerMonad Identity where
>   Elem a1 (Id a2) = a1 = a2
>   tagElem (Id a) = Id (a ** Refl)
>   All P (Id a) = P a
>   spec1 = Refl
>   spec2 {x = x1} {mx = Id x2} {mmx = Id (Id x3)} x1eqx2 idx2eqidx3 =
>     trans x1eqx2 (injectiveId idx2eqidx3)
>   spec3 {mx = Id x} = Refl
>   spec4  {x = x1} {mx = Id x2} {P = P} px2 x1eqx2 = replace (sym x1eqx2) px2

> -}

Container monad decidability:

> ||| |Elem| is decidable
> decElem : {A : Type} -> DecEq0 A -> (a : A) -> (ma : Identity A) -> Dec (a `Elem` ma)
> decElem dec a1 (Id a2) with (dec a1 a2)
>   | (Yes prf)   = Yes prf
>   | (No contra) = No contra

Container monad uniqueness:

> ||| |Elem| is unique
> uniqueElem : {A : Type} -> UniqueEq0 A -> (a : A) -> (ma : Identity A) -> Unique (a `Elem` ma)
> uniqueElem unique a1 (Id a2) p q = unique a1 a2 p q

Show

> using (A : Type)
>   implementation (Show A) => Show (Identity A) where
>     show (Id a) = show a
