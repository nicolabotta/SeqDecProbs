> import Data.Vect
> import Data.Fin

> %default total

> idSuccPreservesLTE : (m : Nat) -> (n : Nat) -> m `LTE` n -> m `LTE` (S n)
> idSuccPreservesLTE  Z     n    prf = LTEZero
> idSuccPreservesLTE (S m)  Z    prf = absurd prf
> idSuccPreservesLTE (S m) (S n) prf = LTESucc (idSuccPreservesLTE m n (fromLteSucc prf))

> ltZS : (m : Nat) -> LT Z (S m)
> ltZS  Z    = LTESucc LTEZero
> ltZS (S m) = idSuccPreservesLTE (S Z) (S m) (ltZS m)

> data TotalPreorder : Type -> Type where
>   MkTotalPreorder : {A : Type} ->
>                     (R : A -> A -> Type) ->
>                     (reflexive : (x : A) -> R x x) ->
>                     (transitive : (x : A) -> (y : A) -> (z : A) -> R x y -> R y z -> R x z) ->
>                     (totalPre : (x : A) -> (y : A) -> Either (R x y) (R y x)) ->
>                     TotalPreorder A

> R : {A : Type} -> TotalPreorder A -> (A -> A -> Type)
> R (MkTotalPreorder R _ _ _) = R

> totalPre : {A : Type} ->
>          (tp : TotalPreorder A) ->
>          (x : A) -> (y : A) -> Either ((R tp) x y) ((R tp) y x)
> totalPre (MkTotalPreorder _ _ _ totalPre) = totalPre

> argmaxMax : {A : Type} ->
>             TotalPreorder A -> Vect n A -> LT Z n -> (Fin n, A)
> argmaxMax {n = Z}       tp  Nil                p = absurd p
> argmaxMax {n = S Z}     tp (a :: Nil)          _ = (FZ, a)
> argmaxMax {n = S (S m)} tp (a' :: (a'' :: as)) _ with (argmaxMax tp (a'' :: as) (ltZS m))
>   | (k, max) with ((totalPre tp) a' max)
>     | (Left  _) = (FS k, max)
>     | (Right _) = (FZ, a')
