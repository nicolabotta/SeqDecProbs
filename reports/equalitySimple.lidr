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

> postulate lala : (b : Nat) -> (i : Nat) -> (j : Nat) ->
>                  (p : LT i b) -> (q : LT j b) -> i = j -> p = q

> P : Nat -> Type
> P n = LT n 5

> T : Type
> T = Sigma Nat P

> i : Nat
> i = Z

> j : Nat
> j = Z

> p : P i
> q : P j

> m : T
> m = (i ** p)

> n : T
> n = (j ** q)

> peq : p = q
> peq = lala 5 i j p q Refl

> r : m = n
> r = depCong2 {alpha = Nat} 
>              {P = P} 
>              {a1 = i} 
>              {a2 = j} 
>              {Pa1 = p} 
>              {Pa2 = q} 
>              MkSigma Refl peq

 
