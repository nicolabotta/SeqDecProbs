> module Unique -- from an idea by Tim Richter


> %default total


> Unique : Type -> Type
> Unique t = (p : t) -> (q : t) -> p = q

> Unique0 : Type -> Type
> Unique0 = Unique

> Unique1 : (t0 -> Type) -> Type
> Unique1 {t0} t1 = (v : t0) -> Unique0 (t1 v) 

> {- Maybe implement via a type class ?

> class Unique t where
>   unique : (p : t) -> (q : t) -> p = q 
 
> -}




> {-

> sigmaPropLemma : (P : t -> Type) -> 
>                  (x : Sigma t P) -> 
>                  (y : Sigma t P) ->
>                  getWitness x = getWitness y -> 
>                  IsProp (P (getWitness x)) ->
>                  x = y
> sigmaPropLemma P (a ** p) (a ** q) refl h = cong (sp p q) where
>   sp : (pa : P a) -> (pa' : P a) -> pa = pa'
>   sp = singletonProof h

> sigmaPropLemma : {P : alpha -> Type} -> 
>                  ((a : alpha) -> IsProp (P a)) ->
>                  (s1 : Sigma alpha P) -> 
>                  (s2 : Sigma alpha P) ->
>                  getWitness s1 = getWitness s2 -> 
>                  s1 = s2
> sigmaPropLemma h (a ** p1) (a ** p2) refl = cong (sp p1 p2) where
>   sp : (pa : P a) -> (pa' : P a) -> pa = pa'
>   sp = singletonProof (h a) 

> -- -}
 
