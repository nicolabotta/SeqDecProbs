> module SigmaProperties


> import Decidable
> import Proposition


> %default total


> sigmaLemma1 : {alpha : Type} ->
>               {P : alpha -> Type} -> 
>               (x : Sigma alpha P) -> 
>               (y : Sigma alpha P) ->
>               getWitness x = getWitness y -> 
>               Prop (P (getWitness x)) ->
>               x = y
> sigmaLemma1 (a ** p) (a ** q) Refl PP = cong (PP p q)

> sigmaLemma2 : {alpha : Type} ->
>               {P : alpha -> Type} -> 
>               (x : Sigma alpha P) -> 
>               (y : Sigma alpha P) ->
>               (x = y) ->
>               (getWitness x = getWitness y)

> sigmaLemma2 (a ** p) (a ** p) Refl = Refl

> sigmaLemma3 : {alpha : Type} ->
>               {P : alpha -> Type} ->
>               DecEq alpha -> 
>               Prop1 {alpha} P ->
>               (s1 : Sigma alpha P) ->
>               (s2 : Sigma alpha P) ->
>               Dec (s1 = s2)
> sigmaLemma3 da p1P s1 s2 with (decEq (getWitness s1) (getWitness s2)) 
>   | (Yes prf) = Yes (sigmaLemma1 s1 s2 prf (p1P (getWitness s1)))
>   | (No contra) = No (\ eq => contra (sigmaLemma2 s1 s2 eq))

