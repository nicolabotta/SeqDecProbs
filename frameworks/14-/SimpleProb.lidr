> module SimpleProb

> import Data.Vect

> import NonNegRational
> import NonNegRationalOperations
> import NonNegRationalProperties

> -- import Syntax.PreorderReasoning
> import NatPositive
> -- import Fraction
> import FractionNormal
> -- import FractionOperations
> -- import FractionProperties
> -- import PairsOperations
> -- import NatOperations
> -- import NatProperties
> -- import NatCoprime
> -- import NatDivisor
> -- import NatDivisorOperations
> -- import NatDivisorProperties
> -- import NatGCD
> -- import NatGCDOperations
> -- import NatGCDEuclid
> -- import Sigma

> %default total

> %access public export

> -- %freeze NonNegRational


> |||
> data SimpleProb : Type -> Type where
>   MkSimpleProb : {A : Type} -> 
>                  (as : Vect n A) ->
>                  (ps : Vect n NonNegRational) ->
>                  sum ps = 1 ->
>                  SimpleProb A


* Operations

> prob : (Eq alpha) => SimpleProb alpha -> alpha -> NonNegRational
> prob (MkSimpleProb as pa _) a = foldr f 0 (zip as pa) where
>   f : (alpha, NonNegRational) -> NonNegRational -> NonNegRational
>   f (a', p') p = if (a == a') then p + p' else p
> -- %freeze prob


> {-


* Properties

|SimpleProb| is a functor:

> fmap : {A, B : Type} -> (A -> B) -> SimpleProb A -> SimpleProb B
> fmap f (MkSimpleProb as ps p) = MkSimpleProb (map f as) ps p

|SimpleProb| is a monad:

> ret : {A : Type} -> A -> SimpleProb A
> ret {A} a = MkSimpleProb as ps p where
>   n  : Nat
>   n  = S Z
>   as : Vect n A
>   as = a :: Nil
>   ps : Vect n NonNegQ
>   ps = oneNonNegQ :: Nil
>   p  : sum ps = oneNonNegQ
>   p  = sumLemma0 oneNonNegQ

> {-
> bind : {A, B : Type} -> SimpleProb A -> (A -> SimpleProb B) -> SimpleProb B
> bind {A} {B} (MkSimpleProb as ps p) f = MkSimpleProb bs ps' p' where
>   n  : Nat
>   n  = length as
>   bs : Vect n B
> -}


> ---}
