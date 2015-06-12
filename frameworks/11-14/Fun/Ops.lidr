> module Ops

> import Data.So

> import Logic.Properties
> import Rel.EqEq
> import Rel.ReflEqEq
> import Rel.DecEq
> import Rel.ReflDecEq


> %default total


> modifyFun : (EqEq alpha) => 
>             (alpha -> beta) -> 
>             (alpha, beta) -> 
>             (alpha -> beta)
> modifyFun f (a, b) a' = if a' == a then b else f a'

> modifyFunLemma : (ReflEqEq alpha) => 
>                  (f : alpha -> beta) ->
>                  (ab : (alpha, beta)) ->
>                  modifyFun f ab (fst ab) = snd ab
> modifyFunLemma f (a,b) = 
>   replace {P = \ z => ifThenElse (a == a) b (f a) = ifThenElse z b (f a)} 
>           (soTrue (reflexive_eqeq a)) Refl

> modifyDepFun' : (DecEq.DecEq alpha) => 
>                 {beta : alpha -> Type} ->
>                 ((a : alpha) -> beta a) ->
>                 (ab : (a : alpha ** beta a)) ->
>                 (a' : alpha) ->
>                 Either (getWitness ab = a') (Not (getWitness ab = a')) ->
>                 beta a' 
> modifyDepFun' f (a ** b) a' (Left t)  = replace t b
> modifyDepFun' f (a ** b) a' (Right r) = f a'

> modifyDepFun : (DecEq.DecEq alpha) => 
>                {beta : alpha -> Type} ->
>                ((a : alpha) -> beta a) -> 
>                (a : alpha ** beta a) -> 
>                ((a : alpha) -> beta a)
> modifyDepFun f (a ** b) a' = modifyDepFun' f (a ** b) a' (dec_eq a a')

> modifyDepFunLemma : (ReflDecEq alpha) => 
>                     {beta : alpha -> Type} ->
>                     (f : (a : alpha) -> beta a) -> 
>                     (ab : (a : alpha ** beta a)) ->
>                     modifyDepFun f ab (getWitness ab) = getProof ab

> modifyDepFunLemma f (a ** b) = s2 where
>   s0 : modifyDepFun' f (a ** b) a (Left Refl) = b
>   s0 = Refl
>   s1 : modifyDepFun' f (a ** b) a (Left Refl) = modifyDepFun f (a ** b) a
>   s1 = replace {a = Either (a = a) (Not (a = a))} 
>                {x = a `dec_eq` a}
>                {y = Left Refl}
>                {P = \ z => modifyDepFun' f (a ** b) a z = modifyDepFun f (a ** b) a}
>                (reflexive_dec_eq a) Refl
>   s2 : modifyDepFun f (a ** b) a = b
>   s2 = trans (sym s1) s0

> modifyDepFunLemma1 : (DecEq.DecEq alpha) => 
>                      {beta : alpha -> Type} ->
>                      (f : (a : alpha) -> beta a) -> 
>                      (a : alpha) ->
>                      modifyDepFun f (a ** f a) = f

