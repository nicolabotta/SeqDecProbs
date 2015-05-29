> module Prob

> import Data.Vect


> %default total


> data Prob : Type -> Type where
>   mkProb : (as : Vect n a) -> (ps : Vect n Float) -> sum ps = 1.0 -> Prob a
