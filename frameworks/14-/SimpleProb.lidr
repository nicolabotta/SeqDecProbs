> module SimpleProb

> -- import Data.Vect
> -- import Data.List

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties


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
> %auto_implicits off

> %freeze sum
> %freeze cross
> %freeze mapSndMapCrossAnyIdLemma
> %freeze sumSingletonLemma

> |||
> data SimpleProb : Type -> Type where
>   MkSimpleProb : {alpha : Type} -> 
>                  (aps : List (alpha, NonNegRational)) ->
>                  sum (map snd aps) = 1 ->
>                  SimpleProb alpha

* Operations

> ||| 
> prob : {alpha : Type} -> (Eq alpha) => SimpleProb alpha -> alpha -> NonNegRational
> prob (MkSimpleProb aps _) a = foldr f 0 aps where
>   f : (alpha, NonNegRational) -> NonNegRational -> NonNegRational
>   f (a', p') p = if (a == a') then p + p' else p


* Properties

|SimpleProb| is a functor:

> fmap : {A, B : Type} -> (A -> B) -> SimpleProb A -> SimpleProb B
> fmap f (MkSimpleProb aps p) = 
>   MkSimpleProb (map (cross f id) aps) s4 where
>     s1 : map snd (map (cross f id) aps) = map snd aps
>     s1 = mapSndMapCrossAnyIdLemma f aps
>     s2 : sum (map snd (map (cross f id) aps)) = sum (map snd aps)
>     s2 = cong s1
>     s3 : sum (map snd aps) = 1
>     s3 = p
>     s4 : sum (map snd (map (cross f id) aps)) = 1
>     s4 = trans s2 s3


|SimpleProb| is a monad:

> ret : {A : Type} -> A -> SimpleProb A
> ret {A} a = MkSimpleProb aps s1 where
>   aps : List (A, NonNegRational)
>   aps = [(a,1)]
>   s1  : sum (map snd aps) = 1
>   s1  = sumSingletonLemma 1


> {-

> |||
> bind : {A, B : Type} -> SimpleProb A -> (A -> SimpleProb B) -> SimpleProb B
> bind {A} {B} (MkSimpleProb aps p) f = MkSimpleProb bps q where
>   bps : List (B, NonNegRational)
>   bps = concat (map g aps) where
>     g : (A, NonNegRational) -> List (B, NonNegRational)
>     g (a, pa) = map (\ bpb => (fst bpb, pa * (snd bpb))) (f a)
>   q : sum (map snd bps) = 1
>   q = ?ququ

> ---}
