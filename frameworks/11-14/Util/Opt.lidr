> module Opt

> import Data.So
> import Data.Vect

> import Logic.Properties

> %default total

> max2' : (alpha, Float) -> 
>         (alpha, Float) -> 
>         (alpha, Float)
> max2' a b = if (snd a < snd b) then b else a

> max3' : (alpha, Float) -> 
>         (alpha, Float) -> 
>         (alpha, Float) -> 
>         (alpha, Float)
> max3' a b c = max2' a (max2' b c)

> maxP : Vect (S n) (alpha, Float) -> (alpha, Float)
> maxP (af :: afs) = foldr max2' af afs

> maxP' : (Vect n (alpha, Float), So (Z < n)) -> (alpha, Float)
> maxP' {n = Z} (Nil, ZltZ)         =  soFalseElim ZltZ
> maxP' {n = S n} ((af :: afs), _)  =  foldr max2' af afs



