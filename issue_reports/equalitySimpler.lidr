> cong2 : (f : a -> b -> c) -> (a1 = a2) -> (b1 = b2) -> f a1 b1 = f a2 b2
> cong2 f Refl Refl = Refl

> depCong2 : {alpha : Type} -> 
>            {P : alpha -> Type} ->
>            {a1 : alpha} -> 
>            {a2 : alpha} ->
>            {Pa1 : P a1} ->
>            {Pa2 : P a2} -> 
>            (f : (a : alpha) -> P a -> c) -> 
>            (a1 = a2) ->
>            (Pa1 = Pa2) -> 
>            f a1 Pa1 = f a2 Pa2
> depCong2 f Refl Refl = Refl

> P : Nat -> Type
> P n = LT n 5

> T : Type
> T = Sigma Nat P

> p : P Z
> p = LTESucc LTEZero

> m : T
> m = (Z ** p)

> n : T
> n = (Z ** p)

> q : m = n
> q = depCong2 MkSigma Refl Refl

 
