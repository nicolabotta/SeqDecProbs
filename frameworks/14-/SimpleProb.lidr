> module SimpleProb

> import Data.So
> import Data.Fin
> import Data.Vect
> import Data.Sign

> import Rational
> import NonNegRational
> import SignProperties

> %default total


> data SimpleProb : Type -> Type where
>   MkSimpleProb : {A : Type} -> 
>                  (as : Vect n A) ->
>                  (ps : Vect n NonNegQ) ->
>                  sum ps = 1 ->
>                  SimpleProb A

|SimpleProb| is a functor:

> fmap : {A, B : Type} -> (A -> B) -> SimpleProb A -> SimpleProb B
> fmap f (MkSimpleProb as ps p) = MkSimpleProb (map f as) ps p
