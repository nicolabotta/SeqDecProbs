> module Stochastic

> import Data.So
> import Data.Fin
> import Data.Vect
 
> %default total 


> data Prob : Type -> Type where
>   MkProb  :  {A : Type} ->
>              (as : Vect n A) -> 
>              (ps : Vect n Double) ->
>              (k : Fin n -> So (index k ps >= 0.0)) ->
>              sum ps = 1.0 -> 
>              Prob A 

> X : (t : Nat) -> Type

> Y : (t : Nat) -> (x : X t) -> Type

> step : (t : Nat) -> (x : X t) -> (y : Y t x) -> Prob (X (S t))

> reward : (t : Nat) -> (x : X t) -> (y : Y t x) -> (x' : X (S t)) -> Double

> fmap : {A, B : Type} -> (A -> B) -> Prob A -> Prob B
> fmap f (MkProb as ps p q) = MkProb (map f as) ps p q

> rewards : (t : Nat) -> (x : X t) -> (y : Y t x) -> Prob Double
> rewards t x y = fmap (reward t x y) (step t x y)

> One : Vect 1 Double
> One = [1.0]

> lala : (k : Fin 1) -> So (index k One >= 0.0)

> certain : {A : Type} -> A -> Prob A
> certain a = MkProb [a] [1.0] (lala) Refl

