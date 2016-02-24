> module SimpleProb

> -- import Data.Vect
> -- import Data.List

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
> import NumRefinements
> import NumProperties
> import FunOperations
> import ListProperties

> %default total

> %access public export


> |||
> data SimpleProb : Type -> Type where
>   MkSimpleProb : {alpha : Type} -> 
>                  (aps : List (alpha, NonNegRational)) ->
>                  sum (map snd aps) = 1 ->
>                  SimpleProb alpha


* Operations

> ||| 
> prob : (Eq alpha) => SimpleProb alpha -> alpha -> NonNegRational
> prob (MkSimpleProb aps _) a = foldr f 0 aps where
>   f : (alpha, NonNegRational) -> NonNegRational -> NonNegRational
>   f (a', p') p = if (a == a') then p + p' else p
> %freeze prob


* Properties

|SimpleProb| is a functor:

> fmap : {A, B : Type} -> (A -> B) -> SimpleProb A -> SimpleProb B
> fmap f (MkSimpleProb aps p) = 
>   MkSimpleProb (map (cross f id) aps) s4 where
> {-
>     s1 : map snd (map (cross f id) aps) = map snd aps
>     s1 = ?s1res -- mapSndMapCrossAnyIdLemma f aps
>     s2 : sum (map snd (map (cross f id) aps)) = sum (map snd aps)
>     s2 = ?s2res -- cong s1
>     s3 : sum (map snd aps) = 1
>     s3 = ?s3res -- p
> -}
>     s4 : sum (map snd (map (cross f id) aps)) = 1
>     s4 = ?s4res -- trans s2 s3


> {-

|SimpleProb| is a monad:

> ret : {A : Type} -> A -> SimpleProb A
> ret {A} a = MkSimpleProb as ps s1 where
>   as  :  Vect 1 A
>   as  =  a :: Nil
>   ps  :  Vect 1 NonNegRational
>   ps  =  1 :: Nil
>   s1  :  sum ps = 1
>   s1  =  lemma0 1

> bind : {A, B : Type} -> SimpleProb A -> (A -> SimpleProb B) -> SimpleProb B
> {-
> bind {A} {B} (MkSimpleProb as ps p) f = MkSimpleProb bs ps' p' where
>   n  : Nat
>   n  = length as
>   bs : Vect n B
> -}


> ---}
