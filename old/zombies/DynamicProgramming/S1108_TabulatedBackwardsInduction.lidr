> module TabulatedBackwardsInduction


> import Nat.Postulates
> import Float.Postulates
> import Float.Properties
> import BoundedNat.Blt
> import Logic.Properties
> import Vect.Ops
> import DynamicProgramming.S1101_Context
> import DynamicProgramming.S1102_OptimalControls
> import DynamicProgramming.S1103_OptimalPolicies
> import DynamicProgramming.S1104_MaxArgmax
> import DynamicProgramming.S1105_BackwardsInduction
> import DynamicProgramming.S1107_FiniteState

> %default total


# linear algorithm, vector based:

> tabulatedOptExtension : Vect nX Float -> Policy
> tabulatedOptExtension vt x = argmax x f where
>   f : Y x -> Float  
>   f y = reward x y x' + idx vt i' where
>     x' : X
>     x' = step x y
>     i' : Blt nX
>     i' = index x'

> %assert_total
> tbi : (m : Nat) ->
>       (n: Nat) -> 
>       so (m <= n) -> 
>       PolicySeq m -> 
>       Vect nX Float -> 
>       PolicySeq n
> tbi m n mlten ps vt = 
>   if (m == n) 
>   then believe_me ps
>   else tbi (S m) n (believe_me oh) (p :: ps) vt' where
>     p : Policy
>     p = tabulatedOptExtension vt
>     vt' : Vect nX Float
>     vt' = toVect v' where 
>       v' : Blt nX -> Float
>       v' i = reward x y x' + idx vt i' where
>         x : X
>         x = xedni i
>         y : Y x
>         y = p x
>         x' : X
>         x' = step x y
>         i' : Blt nX
>         i' = index x'

> tabulatedBackwardsInduction : (n : Nat) -> PolicySeq n
> tabulatedBackwardsInduction n = tbi Z n lemma1 Nil (toVect (\ i => 0))


