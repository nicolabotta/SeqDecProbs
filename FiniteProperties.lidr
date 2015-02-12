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
> -- import Unique
> -- import SigmaProperties


> %default total 


> ||| |toVect| representations of finite types are complete
> toVectComplete : {A : Type} -> (fA : Finite A) -> (a : A) -> Elem a (toVect fA)
> toVectComplete fA a = s3 where
>   s1  :  Elem (fromFin fA (toFin fA a)) (toVect fA)
>   s1  =  toVectComplete (fromFin fA) (toFin fA a) 
>   s2  :  fromFin fA (toFin fA a) = a
>   s2  =  FromFinToFin fA a
>   s3  :  Elem a (toVect fA)
>   s3  =  replace {P = \ z => Elem z (toVect fA)} s2 s1


Finiteness implies decidability: We want to show that

< finiteDecLemma : {A : Type} -> {P : A -> Prop} -> Finite A -> Dec1 P -> Dec (Exists P)

It is useful to recall that if a predicate |P : A -> Prop| is decidable,
we have a decision procedure to assess whether in a vector of of type
|A| there exists an element that fulfills |P|:

> decAny : {A : Type} -> {P : A -> Prop} -> Dec1 P -> Dec1 (Any P)
> decAny d1P = any d1P

Further, it is useful to remember (see "VectProperties.lidr") that

< AnyExistsLemma : {A : Type} -> {P : A -> Prop} -> Any P as -> Exists P
< ElemAnyLemma : {A : Type} -> {P : A -> Prop} -> P a -> Elem a as -> Any P as

With these premises, proving |finiteDecLemma| is straightforward:

> finiteDecLemma : {A : Type} -> {P : A -> Prop} -> Finite A -> Dec1 P -> Dec (Exists P)
> finiteDecLemma fA dP with (decAny dP (toVect fA))
>   | (Yes prf)   = Yes (AnyExistsLemma prf)
>   | (No contra) = No (\ e => contra (ElemAnyLemma (getProof e) (toVectComplete fA (getWitness e))))





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
