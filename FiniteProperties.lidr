> module FiniteProperties

> import Data.Fin
> import Data.Vect
> import Data.Vect.Quantifiers
> import Control.Isomorphism

> import Prop
> import Finite
> import FiniteOperations
> import Decidable
> import FinOperations
> import FinProperties
> import VectProperties
> import IsomorphismOperations


> %default total 

> -- toVectComplete : {A : Type} -> (f : Fin n -> A) -> (k : Fin n) -> Elem (f k) (toVect f)


> ||| |toVect| representations of finite types are complete
> toVectComplete : {A : Type} -> (fA : Finite A) -> (a : A) -> Elem a (toVect fA)
> toVectComplete (Evidence n iso) a = s3 where
>   s1  :  Elem (from iso (to iso a)) (toVect (from iso))
>   s1  =  toVectComplete (from iso) (to iso a) 
>   s2  :  from iso (to iso a) = a
>   s2  =  fromTo iso a
>   s3  :  Elem a (toVect (from iso))
>   s3  =  replace {P = \ z => Elem z (toVect (from iso))} s2 s1
> {-
> toVectComplete fA a = s3 where
>   s1  :  Elem (fromFin fA (toFin fA a)) (toVect fA)
>   s1  =  FinProperties.toVectComplete (fromFin fA) (toFin fA a) 
>   s2  :  fromFin fA (toFin fA a) = a
>   s2  =  FromFinToFin fA a
>   s3  :  Elem a (toVect fA)
>   s3  =  replace {P = \ z => Elem z (toVect fA)} s2 s1
> -}


We want to show that, for a finite type |A| and a decidable predicate |P
: A -> Prop|, |Exists P| is decidable

< finiteDecLemma : {A : Type} -> {P : A -> Prop} -> Finite A -> Dec1 P -> Dec (Exists P)

It is useful to recall (see "VectProperties.lidr") that

< decAny         : {A : Type} -> {P : A -> Prop} -> Dec1 P -> Dec1 (Any P)
< AnyExistsLemma : {A : Type} -> {P : A -> Prop} -> Any P as -> Exists P
< ElemAnyLemma   : {A : Type} -> {P : A -> Prop} -> P a -> Elem a as -> Any P as

With these premises, proving |finiteDecLemma| is almost straightforward:

> finiteDecLemma : {A : Type} -> {P : A -> Prop} -> Finite A -> Dec1 P -> Dec (Exists P)
> finiteDecLemma fA dP with (decAny dP (toVect fA))
>   | (Yes prf)   = Yes (AnyExistsLemma prf)
>   | (No contra) = No (\ e => contra (ElemAnyLemma (getProof e) (toVectComplete fA (getWitness e))))

We pattern match on |decAny dP (toVect fA)|: the result is either a |prf
: Any P (toVect fA)| or a function |contra : Any P (toVect fA) ->
Void|. In the first case we just apply |AnyExistsLemma| to |prf|. This
gives us a value of type |Exists P| which is what we need. In the second
case we have to implement a function of type |Exists P -> Void|. We do
this by applying |contra|. To this end, we need a value of type |Any P
(toVect fA)|. We compute a value of type |Any P (toVect fA)| by applying
|ElemAnyLemma|.



> {-


Properties preserve finiteness: We want to show that

< lala : {alpha : Type} -> 
<        {P : alpha -> Type} ->
<        Finite alpha -> 
<        Dec1 {alpha} P -> 
<        Unique1 {alpha} P -> 
<        Finite (Sigma alpha P)

The idea is to start by noticing the one can implement a function 


> asSigmaVectLemma : {alpha : Type} ->
>                    {P : alpha -> Type} ->
>                    (fA : Finite alpha) -> 
>                    (dp : Dec1 {alpha} P) -> 
>                    (s  : Sigma alpha P) -> 
>                    Elem s (getProof (asSigmaVect fA dp))

> -}

With |asSigmaVect| and |asSigmaVectLemma| one can implement

> {-
> lala : {alpha : Type} -> 
>        {Q : alpha -> Type} ->
>        Finite alpha -> 
>        Dec1 {alpha} Q -> 
>        Prop1 {alpha} Q -> 
>        Finite (Sigma alpha Q)
> lala {alpha} {Q} fA dp pp = Evidence n iso where
>   n  : Nat
>   n  = getWitness (asSigmaVect fA dp)
>   ss : Vect n (Sigma alpha Q)
>   ss = getProof (asSigmaVect fA dp)
>   iso : Iso (Sigma alpha Q) (Fin n)
>   iso = MkIso to from toFrom fromTo where
>       to      :  Sigma alpha Q -> Fin n
>       to s    =  lookup s ss (asSigmaVectLemma fA dp  s)
>       from    :  Fin n -> Sigma alpha Q
>       from k  =  index k ss 
>       toFrom  :  (k : Fin n) -> to (from k) = k
>       toFrom k = ?kika where
>         s1 : to (from k)
>              =
>              lookup (index k ss) ss (asSigmaVectLemma fA dp (index k ss))
>         s1 = Refl
>         s2 : lookup (index k ss) ss (asSigmaVectLemma fA dp (index k ss))
>              =
>              k
>         s2 = lookupIndexLemma k ss (asSigmaVectLemma fA dp (index k ss))
>       fromTo  :  (s : Sigma alpha Q) -> from (to s) = s
>       fromTo  =  ?mkFromTo
> -}

> {-
> lookupIndexLemma : (k : Fin n) ->
>                    (xs : Vect n t) ->
>                    lookup (index k xs) xs (indexLemma k xs) = k
> -}


----

An attempt to port the proof from the Vect world to the Finite world.

> finiteDecLemma2 : {A : Type} -> {P : A -> Prop} -> Finite A -> Dec1 P -> Dec (Exists P)
> finiteDecLemma2 fA dP = ?lala

Pseudo-code: case on the size |n| of the finite set
0: empty set => No 
(n+1): case P (A 0) of
         Yes -> Yes
         No  -> recursive call with slightly smaller Finite

Some helpers needed to map between Dec's etc.

> decIso : {X : Type} -> {Y : Type} -> Iso X Y -> Dec X -> Dec Y
> decIso (MkIso to from _ _) (Yes x) = Yes (to x)
> decIso (MkIso to from _ _) (No nx) = No (nx . from)

In fact, Iso is not needed - we can map already with just any pair of functions:

> decIso' : {X : Type} -> {Y : Type} -> (to : X -> Y) -> (from : Y -> X) -> Dec X -> Dec Y
> decIso' to from (Yes x) = Yes (to x)
> decIso' to from (No nx) = No (nx . from)

This may also be weakened:

> existsIso : {A : Type} -> {P : A -> Type} -> {Q : A -> Type} -> 
>             (allIso : (a : A) -> Iso (P a) (Q a)) -> Iso (Exists P) (Exists Q)
> existsIso allIso = ?hej

> lemmaZ : {A : Type} -> FiniteN Z A -> {P : A -> Prop} -> Dec1 P -> Dec (Exists P)
> lemmaZ (MkIso to from _ _) _ = No (\(Evidence wit pro)=> FinZElim (to wit))

This is roughly where we want to end up:

> lemma : (n : Nat) -> {A : Type} -> FiniteN n A -> {P : A -> Prop} -> Dec1 P -> Dec (Exists P)
> lemma Z     = lemmaZ
> lemma (S n) = ?lalaS

But this simpler version should be possible to extend using decIso:
TODO: continue.

> simpler : (n : Nat) -> (P : Fin n -> Prop) -> Dec1 P -> Dec (Exists P)
> simpler Z P dP = No (\(Evidence wit pro)=> FinZElim wit)
> simpler (S n) P dP with (dP FZ)
>   simpler (S n) P dP | (Yes x) = Yes (Evidence FZ x)
>   simpler (S n) P dP | (No nx) = decIso' ?q ?r (simpler n (\i => P (FS i)) ?uru)
