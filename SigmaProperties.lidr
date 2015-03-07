> module SigmaProperties


> import Data.Fin
> import Data.Vect
> import Control.Isomorphism

> import Decidable
> import Finite
> import Unique
> import SigmaOperations
> import VectOperations
> import VectProperties
> import FiniteOperations
> import FiniteProperties
> import FinOperations


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

> ||| Elimination and formation
> sigmaEqLemma0 : {A : Type} -> 
>                 {P : A -> Type} -> 
>                 (s: Sigma A P) -> 
>                 s = (getWitness s ** getProof s)
> sigmaEqLemma0 (a ** p) = Refl


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

< toVectComplete : {A   : Type} ->
<                  {P   : A -> Type} ->
<                  (fA  : Finite A) -> 
<                  (d1P : Dec1 P) -> 
<                  Unique1 {t0 = A} P ->
<                  (s   : Sigma A P) -> 
<                  Elem s (getProof (toVect fA d1P))

We start by deriving two auxiliary results. The first one is

> toVectLemma : {A : Type} ->
>               {P : A -> Type} ->
>               (fA : Finite A) -> 
>               (d1P : Dec1 P) ->
>               (a : A) ->
>               (p : P a) ->
>               Elem a (map Sigma.getWitness (getProof (toVect fA d1P))) 
> toVectLemma {A} {P} fA d1P a p = filterTagLemma d1P a (toVect fA) (toVectComplete fA a) p

The proof is computed by applying |VectProperties.filterTagLemma|:

< filterTagLemma : {A : Type} -> {P : A -> Type} ->
<                  (d1P : Dec1 P) ->
<                  (a : A) ->
<                  (as : Vect n A) ->
<                  Elem a as ->
<                  (p : P a) ->
<                  Elem a (map Sigma.getWitness (getProof (filterTag d1P as)))

to |d1P|, |a|, to the vector-based representation of |A| associated to
|fA| provided by |FiniteOperations.toVect fA| and to a proof that |a| is
an element of |FiniteOperations.toVect fA|. The latter follows from
completeness of |toVect|, see |FiniteProperties.toVectComplete|. In this
form, |toVectLemma| does not type check.

The second result is

> sigmaUniqueLemma1 : {A   : Type} ->
>                     {P   : A -> Type} ->
>                     Unique1 {t0 = A} P ->
>                     (a : A) ->
>                     (p : P a) ->
>                     (ss : Vect n (Sigma A P)) ->
>                     Elem a (map getWitness ss) -> 
>                     Elem (a ** p) ss
> sigmaUniqueLemma1 u1P a p Nil prf = absurd prf
> sigmaUniqueLemma1 u1P a p ((a ** q) :: ss) (Here {x = a}) with (u1P a p q) 
>   sigmaUniqueLemma1 u1P a p ((a ** p) :: ss) (Here {x = a}) | Refl = 
>     Here {x = (a ** p)} {xs = ss}
> sigmaUniqueLemma1 u1P a1 p1 ((a2 ** p2) :: ss) (There prf) = 
>   There (sigmaUniqueLemma1 u1P a1 p1 ss prf)

With |toVectLemma| and |sigmaUniqueLemma1|, it is easy to show that
|toVect| is complete:

> toVectComplete : {A   : Type} ->
>                  {P   : A -> Type} ->
>                  (fA  : Finite A) -> 
>                  (d1P : Dec1 P) -> 
>                  Unique1 {t0 = A} P ->
>                  (s   : Sigma A P) -> 
>                  Elem s (getProof (toVect fA d1P))
> toVectComplete fA d1P u1P (a ** p) = s1 where
>   s0 : Elem a (map Sigma.getWitness (getProof (toVect fA d1P)))
>   s0 = toVectLemma fA d1P a p
>   s1 : Elem (a ** p) (getProof (toVect fA d1P))
>   s1 = sigmaUniqueLemma1 u1P a p (getProof (toVect fA d1P)) s0



Sigma Fin properties:

> using (P : Fin Z -> Type)
>   instance Uninhabited (Sigma (Fin Z) P) where
>     uninhabited (MkSigma k _) = absurd k


> ||| |Sigma (Fin Z) P| are void
> voidSigmaFinZ : {P : Fin Z -> Type} -> Iso (Sigma (Fin Z) P) Void
> voidSigmaFinZ = MkIso (\x => void (uninhabited x)) 
>                       (\x => void x)
>                       (\x => void x)
>                       (\x => void (uninhabited x)) 


> ||| Decomposition lemma
> sigmaFinEitherLemma : {n : Nat} -> {f : Fin (S n) -> Nat} ->
>                       Iso 
>                       (Sigma (Fin (S n)) (\ k => Fin (f k))) 
>                       (Either (Fin (f FZ)) (Sigma (Fin n) (\ k => Fin ((tail f) k))))
> sigmaFinEitherLemma {n} {f} = MkIso to from toFrom fromTo where
>   to : (Sigma (Fin (S n)) (\ k => Fin (f k))) ->
>        (Either (Fin (f FZ)) (Sigma (Fin n) (\ k => Fin ((tail f) k))))
>   to (FZ   ** j) = Left j
>   to (FS k ** j) = Right (k ** j)
>   from : (Either (Fin (f FZ)) (Sigma (Fin n) (\ k => Fin ((tail f) k)))) ->
>          (Sigma (Fin (S n)) (\ k => Fin (f k)))
>   from (Left j) = (FZ ** j)
>   from (Right (k ** j)) = (FS k ** j)
>   toFrom : (e : Either (Fin (f FZ)) (Sigma (Fin n) (\ k => Fin ((tail f) k)))) ->
>            to (from e) = e
>   toFrom (Left j) = Refl
>   toFrom (Right (k ** j)) = Refl
>   fromTo : (s : Sigma (Fin (S n)) (\ k => Fin (f k))) -> from (to s) = s
>   fromTo (FZ ** j) = Refl
>   fromTo (FS k ** j) = Refl


> ||| |finDepPairTimes| for dependent pairs
> finDepPairTimes : {n : Nat} -> {f : Fin n -> Nat} ->
>                   Iso (Sigma (Fin n) (\ k => Fin (f k))) (Fin (sum f))
> finDepPairTimes {n = Z} {f} =
>     ( Sigma (Fin Z) (\ k => Fin (f k)) )
>   ={ voidSigmaFinZ }=  
>     ( Void                             )   
>   ={ isoSym finZeroBot }=                                                                           
>     ( Fin Z                            )
>   QED     
> finDepPairTimes {n = S m} {f} =
>     ( Sigma (Fin (S m)) (\ k => Fin (f k))                          )
>   ={ sigmaFinEitherLemma }=
>     ( Either (Fin (f FZ)) (Sigma (Fin m) (\ k => Fin ((tail f) k))) )
>   ={ eitherCongRight (finDepPairTimes {n = m} {f = tail f}) }=
>     ( Either (Fin (f FZ)) (Fin (sum (tail f)))                      )
>   ={ eitherFinPlus }=
>     ( Fin (f FZ + sum (tail f))                                     )
>   ={ isoRefl }=
>     ( Fin (sum f)                                                   )
>   QED



Finitess properties

> ||| For finite predicates, Sigma types of finite types are finite
> finiteSigmaLemma0 : {A : Type} -> {P : A -> Type} ->
>                     Finite A -> Finite1 P -> Finite (Sigma A P)

This should now be implementable in terms of |finDepPairTimes|. We
probably need an intermediate step which constructs an

  Iso (Sigma A P) (Sigma (Fin (card fA)) (\ k => Fin (card (f1P k))))

and then apply |isoTrans|.
