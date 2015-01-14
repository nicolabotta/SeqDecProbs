> module Finite

> import Data.So
> import Data.Fin
> import Data.Vect
> import Data.Vect.Quantifiers
> import Control.Isomorphism


> %default total 


In the context of

> Dec1 : (p : alpha -> Type) -> Type
> Dec1 {alpha} p  =  (a : alpha) -> Dec (p a) 

> Finite : Type -> Type
> Finite alpha = Exists (\ n => Iso alpha (Fin n))

> fromFin : (fa : Finite alpha) -> (Fin (getWitness fa) -> alpha)
> fromFin (Evidence n (MkIso to from toFrom fromTo)) = from

> toFin : (fa : Finite alpha) -> (alpha -> Fin (getWitness fa))
> toFin (Evidence n (MkIso to from toFrom fromTo)) = to

> toFinFromFin : (fa : Finite alpha) -> (k : Fin (getWitness fa)) -> toFin fa (fromFin fa k) = k
> toFinFromFin (Evidence n (MkIso to from toFrom fromTo)) = toFrom

> FromFinToFin : (fa : Finite alpha) -> (a : alpha) -> fromFin fa (toFin fa a) = a
> FromFinToFin (Evidence n (MkIso to from toFrom fromTo)) = fromTo

We want to show that

> finiteDecLemma : Finite alpha -> Dec1 {alpha} p -> Dec (Exists p)


The idea is to start by noticing the one can implement a function 

> asVect : (fa : Finite alpha) -> Vect (getWitness fa) alpha
 
that provides a |Vect|-representation of a finite type in the sense that
it fulfills the specification

> asVectLemma : (fa : Finite alpha) -> (a : alpha) -> Elem a (asVect fa)

A further step is to prove that, for a finite type |alpha| and a
predicate |p| on |alpha|, the existence of an element |a : alpha| in the
vector-representation of |alpha| that satisfies |p| implies |Exists p|:

> AnyExistsLemma : Any p as -> Exists p

The third ingredient which we need to prove |finiteDecLemma| is

> ElemAnyLemma : p a -> Elem a as -> Any p as

With |asVectLemma|, |AnyExistsLemma|, |ElemAnyLemma| and taking into
account that decidability of |p : alpha -> Type| implies decidability of
|Any p|

> decAny : Dec1 p -> Dec1 (Any p)

it is easy to prove |finiteDecLemma|:

> -- finiteDecLemma : Finite alpha -> Dec1 {alpha} p -> Dec (Exists p)
> finiteDecLemma {p} fa dp with (decAny dp (asVect fa))
>   | (Yes prf)   = Yes (AnyExistsLemma prf)
>   | (No contra) = No contra' where
>       contra' :  Exists p -> Void
>       contra' (Evidence a pa) = contra (ElemAnyLemma pa (asVectLemma fa a))


Thus, the question is whether we can implement

< asVect : (fa : Finite alpha) -> Vect (getWitness fa) alpha
< asVectLemma : (fa : Finite alpha) -> (a : alpha) -> Elem a (asVect fa)
< AnyExistsLemma : (fa : Finite alpha) -> (p : alpha -> Type) -> Any p (asVect fa) -> Exists p
< ElemAnyLemma : p a -> Elem a as -> Any p as
< decAny : Dec1 p -> Dec1 (Any p)


# asVect, asVectLemma

> tail : (Fin (S n) -> alpha) -> (Fin n -> alpha)
> tail f k = f (FS k)

> toVect : (Fin n -> alpha) -> Vect n alpha
> toVect {n =   Z} _ = Nil
> toVect {n = S m} f = (f FZ) :: (toVect (tail f)) 

> toVectLemma : (f : Fin n -> alpha) -> (k : Fin n) -> Elem (f k) (toVect f)
> toVectLemma {n = Z} _  k     = void (uninhabited k)
> toVectLemma         f  FZ    = Here
> toVectLemma         f (FS j) = There (toVectLemma (tail f) j)

> -- asVect : (fa : Finite alpha) -> Vect (getWitness fa) alpha
> asVect fa = toVect (fromFin fa)

> -- asVectLemma : (fa : Finite alpha) -> (a : alpha) -> Elem a (asVect fa)
> asVectLemma fa a = s3 where
>   s1  :  Elem (fromFin fa (toFin fa a)) (asVect fa)
>   s1  =  toVectLemma (fromFin fa) (toFin fa a) 
>   s2  :  fromFin fa (toFin fa a) = a
>   s2  =  FromFinToFin fa a
>   s3  :  Elem a (asVect fa)
>   s3  =  replace {P = \ z => Elem z (asVect fa)} s2 s1


# AnyExistsLemma

> -- AnyExistsLemma : Any p as -> Exists p
> AnyExistsLemma (Here {x} px) = Evidence x px 
> AnyExistsLemma (There prf) = AnyExistsLemma prf


# ElemAnyLemma

> -- ElemAnyLemma : p a -> Elem a as -> Any p as
> ElemAnyLemma pa Here = Here pa
> ElemAnyLemma pa (There eaas) = There (ElemAnyLemma pa eaas)


# decAny

> -- decAny : Dec1 p -> Dec1 (Any p)
> decAny dp as = any dp as
