> module Proposition -- from an idea by Tim Richter


> %default total


> Prop : Type -> Type
> Prop P = (p : P) -> (q : P) -> p = q

> Prop0 : Type -> Type
> Prop0 = Prop

> Prop1 : (alpha -> Type) -> Type
> Prop1 {alpha} P = (a : alpha) -> Prop0 (P a) 


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
