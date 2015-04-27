> module Stochastic


> import Data.Vect

 
> %default total 


> data Prob : Type -> Type where
>   MkProb : {A : Type} -> (as : Vect n A) -> (ps : Vect n Float) -> sum ps = 1.0 -> Prob A 

> X : (t : Nat) -> Type

> Y : (t : Nat) -> (x : X t) -> Type

> step : (t : Nat) -> (x : X t) -> (y : Y t x) -> Prob (X (S t))

> reward : (t : Nat) -> (x : X t) -> (y : Y t x) -> (x' : X (S t)) -> Float

> fmap : {A, B : Type} -> (A -> B) -> Prob A -> Prob B
> fmap f (MkProb as ps prf) = MkProb (map f as) ps prf

> rewards : (t : Nat) -> (x : X t) -> (y : Y t x) -> Prob Float
> rewards t x y = fmap (reward t x y) (step t x y)

