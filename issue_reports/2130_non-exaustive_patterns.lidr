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

> namespace lala

>   data Preorder : {T : Type} -> (T -> T -> Type) -> Type where
>     MkPreorder : {T : Type} ->
>                  (R : T -> T -> Type) ->
>                  (reflexive : (x : T) -> R x x) ->
>                  (transitive : (x : T) -> (y : T) -> (z : T) -> R x y -> R y z -> R x z) ->
>                  Preorder R

>   reflexive : {T : Type} -> {R : T -> T -> Type} -> Preorder R -> (x : T) -> R x x
>   reflexive (MkPreorder _ r _) = r

> namespace lulu

>   data TotalPreorder : {T : Type} -> (T -> T -> Type) -> Type where
>     MkTotalPreorder : {T : Type} ->
>                       (R : T -> T -> Type) ->
>                       (reflexive : (x : T) -> R x x) ->
>                       (transitive : (x : T) -> (y : T) -> (z : T) -> R x y -> R y z -> R x z) ->
>                       (totalPre : (x : T) -> (y : T) -> Either (R x y) (R y x)) ->
>                       TotalPreorder R

>   reflexive : {T : Type} -> {R : T -> T -> Type} -> TotalPreorder R -> (x : T) -> R x x
>   reflexive (MkTotalPreorder _ r _ _) = r

> argmaxMax : {A : Type} -> {R : A -> A -> Type} -> TotalPreorder {T = A} R ->
>             Vect n A -> LT Z n -> (Fin n, A)
> argmaxMax         {n = Z}       tp  Nil                p = absurd p
> argmaxMax         {n = S Z}     tp (a :: Nil)          _ = (FZ, a)
> argmaxMax {A} {R} {n = S (S m)} (MkTotalPreorder R r t e) (a' :: (a'' :: as)) _
>   with (argmaxMax (MkTotalPreorder {T = A} R r t e) (a'' :: as) (ltZS m))
>     | (k, max) with (e a' max)
>       | (Left  _) = (FS k, max)
>       | (Right _) = (FZ, a')
