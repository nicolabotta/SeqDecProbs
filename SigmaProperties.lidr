> module SigmaProperties


> import Data.Fin
> import Data.Vect
> import Control.Isomorphism

> import SigmaOperations
> import VectOperations
> import Decidable
> import Finite
> import FiniteOperations
> import Unique


> %default total


Equality of projections:

> ||| Equality of first projections
> getWitnessPreservesEq : {A  : Type} ->
>                         {P  : A -> Type} -> 
>                         {s1 : Sigma A P} -> 
>                         {s2 : Sigma A P} ->
>                         (s1 = s2) -> (getWitness s1 = getWitness s2)
> getWitnessPreservesEq {s1 = (a ** p)} {s2 = (a ** p)} Refl = Refl

> ||| Equality of second projections
> getProofPreservesEq : {A  : Type} ->
>                       {P  : A -> Type} -> 
>                       {s1 : Sigma A P} -> 
>                       {s2 : Sigma A P} ->
>                       (s1 = s2) -> (getProof s1 = getProof s2)
> getProofPreservesEq {s1 = (a ** p)} {s2 = (a ** p)} Refl = Refl


Equality of Sigma types:

> ||| Equality for singleton predicates
> sigmaEqLemma1 : {A  : Type} ->
>                 {P  : A -> Type} -> 
>                 (s1 : Sigma A P) -> 
>                 (s2 : Sigma A P) ->
>                 getWitness s1 = getWitness s2 -> 
>                 Unique0 (P (getWitness s1)) ->
>                 s1 = s2
> sigmaEqLemma1 (a ** p) (a ** q) Refl uP = cong (uP p q)


Decidability of Sigma equality:

> ||| Decidability of equality 1
> sigmaDecEqLemma1 : {A : Type} ->
>                    {P : A -> Type} ->
>                    DecEq0 A -> 
>                    DecEq1 P ->
>                    (s1 : Sigma A P) ->
>                    (s2 : Sigma A P) ->
>                    Dec (s1 = s2)
> sigmaDecEqLemma1 da d1p (a1 ** pa1) (a2 ** pa2)     with (da a1 a2)
>   sigmaDecEqLemma1 da d1p (a1 ** pa1) (a1 ** pa2)   | (Yes Refl) with ((d1p a1) pa1 pa2)
>     sigmaDecEqLemma1 da d1p (a1 ** pa1) (a1 ** pa1) | (Yes Refl) | (Yes Refl) = Yes Refl
>     sigmaDecEqLemma1 da d1p (a1 ** pa1) (a1 ** pa2) | (Yes Refl) | (No contra) = No (\ eq => contra (getProofPreservesEq eq))     
>   sigmaDecEqLemma1 da d1p (a1 ** pa1) (a2 ** pa2)   | (No contra) = No (\ eq => contra (getWitnessPreservesEq eq))


> ||| Decidability of equality 2
> sigmaDecEqLemma2 : {A : Type} ->
>                    {P : A -> Type} ->
>                    DecEq A -> 
>                    Unique1 {t0 = A} P ->
>                    (s1 : Sigma A P) ->
>                    (s2 : Sigma A P) ->
>                    Dec (s1 = s2)
> sigmaDecEqLemma2 da p1P s1 s2 with (decEq (getWitness s1) (getWitness s2)) 
>   | (Yes prf)   = Yes (sigmaEqLemma1 s1 s2 prf (p1P (getWitness s1)))
>   | (No contra) = No (\ eq => contra (getWitnessPreservesEq eq))


We want to show that |toVect| is complete

> ||| |toVect| is complete
> toVectComplete : {A   : Type} ->
>                  {P   : A -> Type} ->
>                  (fA  : Finite A) -> 
>                  (d1P : Dec1 P) -> 
>                  Unique1 {t0 = A} P ->
>                  (s   : Sigma A P) -> 
>                  Elem s (getProof (toVect fA d1P))
> toVectComplete fA d1P u1P (a ** p) = s11 where
>   s01 : Elem a (map getWitnedd (getProof (toVect fA d1P)))
>   s01 = ?lika
>   s11 : Elem (a ** p) (getProof (toVect fA d1P))
>   s11 = ?kika


We start with something simpler



