> %default total

> ||| Introduction
> sigmaEq2 : {A : Type} -> 
>            {P : A -> Type} -> 
>            {s1: Sigma A P} -> 
>            {s2: Sigma A P} ->
>            getWitness s1 = getWitness s2 ->
>            getProof s1 = getProof s2 ->
>            s1 = s2
> sigmaEq2 {A} {P} {s1 = (a ** p)} {s2 = (a ** p)} Refl Refl = Refl


