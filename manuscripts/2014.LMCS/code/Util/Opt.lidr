> module Opt

> import Data.Vect
> import Data.So

> import Logic.Properties

> %default total

> %access public export


> max2' : (alpha, Double) ->
>         (alpha, Double) ->
>         (alpha, Double)
> max2' a b = if (snd a < snd b) then b else a

> max3' : (alpha, Double) ->
>         (alpha, Double) ->
>         (alpha, Double) ->
>         (alpha, Double)
> max3' a b c = max2' a (max2' b c)

> maxP : Vect (S n) (alpha, Double) -> (alpha, Double)
> maxP (af :: afs) = foldr max2' af afs

> maxP' : (Vect n (alpha, Double), So (Z < n)) -> (alpha, Double)
> maxP' {n = Z} (Nil, ZltZ)         =  soFalseElim ZltZ
> maxP' {n = S n} ((af :: afs), _)  =  foldr max2' af afs
