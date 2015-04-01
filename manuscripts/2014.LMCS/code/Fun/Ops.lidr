> module Ops

> -- import Logic.Ops
> import Rel.EqEq
> import Rel.ReflEqEq
> import Rel.DecEq
> import Rel.ReflDecEq

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
>   replace {P = \ z => boolElim (a == a) b (f a) = boolElim z b (f a)} 
>           (soTrue (reflexive_eqeq a)) refl

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
>   s0 : modifyDepFun' f (a ** b) a (Left refl) = b
>   s0 = refl
>   s1 : modifyDepFun' f (a ** b) a (Left refl) = modifyDepFun f (a ** b) a
>   s1 = replace {a = Either (a = a) (Not (a = a))} 
>                {x = a `dec_eq` a}
>                {y = Left refl}
>                {P = \ z => modifyDepFun' f (a ** b) a z = modifyDepFun f (a ** b) a}
>                (reflexive_dec_eq a) refl
>   s2 : modifyDepFun f (a ** b) a = b
>   s2 = trans (sym s1) s0

