> module Finite

> import Data.Fin
> import Data.Vect
> import Data.Vect.Quantifiers
> import Control.Isomorphism

> import Prop
> import Decidable
> import Unique
> import SigmaProperties
> import VectProperties


> %default total 


> Finite : Type -> Type
> Finite A = Exists (\ n => Iso A (Fin n))


Helpers

> toFin : {A : Type} -> (fA : Finite A) -> (A -> Fin (getWitness fA))
> toFin (Evidence n (MkIso to from toFrom fromTo)) = to

> fromFin : {A : Type} -> (fA : Finite A) -> (Fin (getWitness fA) -> A)
> fromFin (Evidence n (MkIso to from toFrom fromTo)) = from

> toFinFromFin : {A : Type} -> (fA : Finite A) -> (k : Fin (getWitness fA)) -> toFin fA (fromFin fA k) = k
> toFinFromFin (Evidence n (MkIso to from toFrom fromTo)) = toFrom

> FromFinToFin : {A : Type} -> (fA : Finite A) -> (a : A) -> fromFin fA (toFin fA a) = a
> FromFinToFin (Evidence n (MkIso to from toFrom fromTo)) = fromTo


Finiteness implies decidability: We want to show that

< finiteDecLemma : {A : Type} -> {P : A -> Prop} -> Finite A -> Dec1 P -> Dec (Exists P)

The idea is to start by noticing the one can implement a function 

> asVect : {A : Type} -> (fA : Finite A) -> Vect (getWitness fA) A
 
that provides a |Vect|-representation of a finite type in the sense that
it fulfills the specification

> asVectLemma : {A : Type} -> (fA : Finite A) -> (a : A) -> Elem a (asVect fA)

A further step is to prove that, for a finite type |alpha| and a
predicate |p| on |alpha|, the existence of an element |a : alpha| in the
vector-representation of |alpha| that satisfies |p| implies |Exists p|:

> AnyExistsLemma : {A : Type} -> {P : A -> Prop} -> Any P as -> Exists P

The third ingredient which we need to prove |finiteDecLemma| is

> ElemAnyLemma : {A : Type} -> {P : A -> Prop} -> P a -> Elem a as -> Any P as

With |asVectLemma|, |AnyExistsLemma|, |ElemAnyLemma| and taking into
account that decidability of |p : alpha -> Type| implies decidability of
|Any p|

> decAny : {A : Type} -> {P : A -> Prop} -> Dec1 P -> Dec1 (Any P)

it is easy to prove |finiteDecLemma|:

> %assert_total
> finiteDecLemma : {A : Type} -> {P : A -> Prop} -> Finite A -> Dec1 P -> Dec (Exists P)
> finiteDecLemma {A} {P} fA dP with (decAny dP (asVect fA))
>   | (Yes prf)   = Yes (AnyExistsLemma prf)
>   | (No contra) = No (\ e => contra (ElemAnyLemma (getProof e) (asVectLemma fA (getWitness e))))

Thus, the question is whether we can implement

< asVect : {A : Type} -> (fA : Finite A) -> Vect (getWitness fA) A
< asVectLemma : {A : Type} -> (fA : Finite A) -> (a : A) -> Elem a (asVect fA)
< AnyExistsLemma : {A : Type} -> {P : A -> Prop} -> Any P as -> Exists P
< ElemAnyLemma : {A : Type} -> {P : A -> Prop} -> P a -> Elem a as -> Any P as
< decAny : {A : Type} -> {P : A -> Prop} -> Dec1 P -> Dec1 (Any P)

and this is quite straightforward:

# asVect, asVectLemma

> tail : {A : Type} -> (Fin (S n) -> A) -> (Fin n -> A)
> tail f k = f (FS k)

> toVect : {A : Type} -> (Fin n -> A) -> Vect n A
> toVect {n =   Z} _ = Nil
> toVect {n = S m} f = (f FZ) :: (toVect (tail f)) 

> toVectLemma : {A : Type} -> (f : Fin n -> A) -> (k : Fin n) -> Elem (f k) (toVect f)
> toVectLemma {n = Z} _  k     = void (uninhabited k)
> toVectLemma         f  FZ    = Here
> toVectLemma         f (FS j) = There (toVectLemma (tail f) j)

> -- asVect : {A : Type} -> (fA : Finite A) -> Vect (getWitness fA) A
> asVect fA = toVect (fromFin fA)

> --  asVectLemma : {A : Type} -> (fA : Finite A) -> (a : A) -> Elem a (asVect fA)
> asVectLemma fA a = s3 where
>   s1  :  Elem (fromFin fA (toFin fA a)) (asVect fA)
>   s1  =  toVectLemma (fromFin fA) (toFin fA a) 
>   s2  :  fromFin fA (toFin fA a) = a
>   s2  =  FromFinToFin fA a
>   s3  :  Elem a (asVect fA)
>   s3  =  replace {P = \ z => Elem z (asVect fA)} s2 s1

# AnyExistsLemma

> -- AnyExistsLemma : {A : Type} -> {P : A -> Prop} -> Any P as -> Exists P
> AnyExistsLemma (Here {x} px) = Evidence x px 
> AnyExistsLemma (There prf) = AnyExistsLemma prf

# ElemAnyLemma

> -- ElemAnyLemma : {A : Type} -> {P : A -> Prop} -> P a -> Elem a as -> Any P as
> ElemAnyLemma p Here = Here p
> ElemAnyLemma p (There e) = There (ElemAnyLemma p e)

# decAny

> -- decAny : {A : Type} -> {P : A -> Prop} -> Dec1 P -> Dec1 (Any P)
> decAny d1P = any d1P


> {-


Properties preserve finiteness: We want to show that

< lala : {alpha : Type} -> 
<        {P : alpha -> Type} ->
<        Finite alpha -> 
<        Dec1 {alpha} P -> 
<        Unique1 {alpha} P -> 
<        Finite (Sigma alpha P)

The idea is to start by noticing the one can implement a function 

> asSigmaVect : {alpha : Type} ->
>               {P : alpha -> Type} ->
>               Finite alpha -> 
>               Dec1 {alpha} P -> 
>               (n ** Vect n (Sigma alpha P))
 

that provides a |Vect|-representation of a subtype of a finite type in
the sense that it fulfills the specification

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
