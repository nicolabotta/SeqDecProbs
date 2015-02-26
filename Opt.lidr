> module Opt


> import Control.Isomorphism
> import Data.Fin
> import Data.Vect
> import Decidable.Order

> import Finite
> import FiniteOperations
> import FiniteProperties
> import Order
> import OrderOperations
> import OrderProperties
> import VectOperations
> import VectProperties
> import Util


> %default total 


> argmaxMax : {A, B : Type} -> {TO : B -> B -> Type} -> 
>             Preordered B TO => 
>             (fA : Finite A) -> (ne : NonEmpty fA) -> 
>             (f : A -> B) -> (A,B)
> argmaxMax {A} {B} {TO} fA nefA f = 
>   VectOperations.max {A = (A,B)} {TO = sndType TO} abs nefA where
>     abs : Vect (card fA) (A,B)
>     abs = map (pair (id, f)) (toVect fA)


> max : {A, B : Type} -> {TO : B -> B -> Type} -> 
>       Preordered B TO => 
>       (fA : Finite A) -> (ne : NonEmpty fA) -> 
>       (f : A -> B) -> B
> max fA nefA f = snd (argmaxMax fA nefA f)


> argmax : {A, B : Type} -> {TO : B -> B -> Type} -> 
>          Preordered B TO => 
>          (fA : Finite A) -> (ne : NonEmpty fA) -> 
>          (f : A -> B) -> A
> argmax fA nefA f = fst (argmaxMax fA nefA f)


> maxSpec : {A, B : Type} -> {TO : B -> B -> Type} -> 
>           Preordered B TO => 
>           (fA : Finite A) -> (nefA : NonEmpty fA) -> 
>           (f : A -> B) ->
>           (a : A) -> TO (f a) (max fA nefA f)
> maxSpec {A} {B} {TO} fA nefA f a = s4 where
>   abs : Vect (card fA) (A,B)
>   abs = map (pair (id, f)) (toVect fA)
>   s1 : Elem (a, f a) abs
>   s1 = mapLemma (toVect fA) (pair (id, f)) a (toVectComplete fA a)
>   s2 : (sndType TO) (a, f a) (VectOperations.max {A = (A,B)} {TO = sndType TO} abs nefA)
>   s2 = maxLemma (a, f a) abs nefA s1
>   s3 : TO (f a) (snd (VectOperations.max {A = (A,B)} {TO = sndType TO} abs nefA))
>   s3 = s2
>   s4 : TO (f a) (max fA nefA f)
>   s4 = s3


> argmaxSpec : {A, B : Type} -> {TO : B -> B -> Type} -> 
>              Preordered B TO => 
>              (fA : Finite A) -> (ne : NonEmpty fA) -> 
>              (f : A -> B) ->
>              (max fA nefA f) = f (argmax fA nefA f)
