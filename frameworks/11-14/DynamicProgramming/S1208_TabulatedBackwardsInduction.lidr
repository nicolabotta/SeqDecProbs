> module TabulatedBackwardsInduction

> import Data.So
> import Data.Vect

> import BoundedNat.Blt
> import Vect.Ops
> import Exists.Ops
> import Logic.Properties
> import Nat.Postulates

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability
> import DynamicProgramming.S1203_OptimalPolicies
> import DynamicProgramming.S1204_MaxArgmax
> import DynamicProgramming.S1205_BackwardsInduction
> import DynamicProgramming.S1207_FiniteState

> %default total

For the case in which the set of states which are reachable in |m| steps
and viable for |n| steps is finite, it is useful to compute an optimal
extension of a function of type |(Blt (nX (S m) n) -> Float)|, see
|tabulatedBackwardsInduction| below.

> tabulatedOptExtension : 
>   (t : Nat) -> 
>   (n : Nat) -> 
>   Vect (nX (S t) n) Float ->
>   Policy t (S n)
> tabulatedOptExtension t n' vt = p where
>   p : Policy t (S n')
>   p x r v = yq where 
>     yq : (y : Y t x ** So (viable n' (step t x y)))
>     yq = argmax n' x r v f where
>       f : (y : Y t x ** So (viable n' (step t x y))) -> Float  
>       f (y ** q) = reward t x y x' + idx vt i' where
>         x' : X (S t)
>         x' = step t x y
>         r' : So (reachable x')
>         r' = reachableSpec1 x r y
>         v' : So (viable n' x')
>         v' = q
>         xrv' : (x'' : X (S t) **
>                (So (reachable x''), So (viable n' x'')))
>         xrv' = (x' ** (r', v'))
>         i' : Blt (nX (S t) n')
>         i' = index n' xrv'

> castPolicySeq : 
>   (i : Nat) ->
>   (j : Nat) ->
>   (k : Nat) ->
>   PolicySeq (i - j) k ->
>   So (j < i) -> 
>   PolicySeq (S (i - S j)) k
> castPolicySeq i j k ps jLTi = leibniz P a1EQa2 ps where
>   P : Nat -> Type
>   P a = PolicySeq a k
>   a1EQa2 : (i - j) = S (i - S j)
>   a1EQa2 = believe_me jLTi -- trivial ?

> castvt : 
>   (i : Nat) ->
>   (j : Nat) ->
>   (k : Nat) ->
>   Vect (nX (i - j) k) Float ->
>   So (j < i) -> 
>   Vect (nX (S (i - S j)) k) Float
> castvt i j k vt jLTi = leibniz P a1EQa2 vt where
>   P : Nat -> Type
>   P a = Vect (nX a k) Float
>   a1EQa2 : (i - j) = S (i - S j)
>   a1EQa2 = believe_me jLTi -- trivial ?

> %assert_total
> tbi : (t : Nat) ->
>       (n : Nat) -> 
>       (c : Nat) ->
>       (clten : So (c <= n)) ->
>       PolicySeq (t + n - c) c ->
>       Vect (nX (t + n - c) c) Float ->
>       PolicySeq t n
> tbi t n1 c clten ps vt =
>   if (c == n1) 
>   then believe_me ps
>   else tbi t n1 c' c'lten ps' vvt' where
>     cltmpn : So (c < m + n1)
>     cltmpn = believe_me Oh
>     c' : Nat
>     c' = S c
>     t' : Nat
>     t' = t + n1 - c'
>     c'lten : So (c' <= n1)
>     c'lten = believe_me Oh
>     p : Policy t' c'
>     p = tabulatedOptExtension t' c (castvt (t + n1) c c vt (believe_me Oh))
>     ps' : PolicySeq t' c'
>     ps' = (p :: (castPolicySeq (t + n1) c c ps cltmpn))
>     vvt' : Vect (nX t' c') Float
>     vvt' = toVect vt' where
>       vt' : Blt (nX t' c') -> Float
>       vt' i = reward t' x y x' + idx (castvt (t + n1) c c vt (believe_me Oh)) i' where
>         %assert_total
>         xrv : (w : X t' ** (So (reachable w), So (viable c' w)))
>         xrv = xedni c' i
>         x : X t'
>         x = outl xrv
>         rv : (So (reachable x), So (viable c' x))
>         rv = outr xrv
>         %assert_total  
>         r : So (reachable x)
>         r = fst rv
>         %assert_total  
>         v : So (viable c' x)
>         v = snd rv
>         %assert_total  
>         y : Y t' x
>         y = outl (p x r v)
>         x' : X (S t')
>         x' = step t' x y
>         r' : So (reachable x')
>         r' = reachableSpec1 x r y
>         %assert_total  
>         v' : So (viable c x')  
>         v' = outr (p x r v)
>         %assert_total  
>         i' : Blt (nX (S t') c)
>         i' = index c (x' ** (r',v'))

> tabulatedBackwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
> tabulatedBackwardsInduction t n = tbi t n Z lemma1 Nil (toVect (\ i => 0))

