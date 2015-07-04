> module TabulatedBackwardsInduction


> import Data.So
> import Data.Vect

> import BoundedNat.Blt
> import Vect.Ops
> import Exists.Ops
> import Logic.Properties
> import Nat.Postulates

> import DynamicProgrammingSmall.S1301_Context
> import DynamicProgrammingSmall.S1302_Reachability
> import DynamicProgrammingSmall.S1302_Viability
> import DynamicProgrammingSmall.S1302_Feasibility
> import DynamicProgrammingSmall.S1303_OptimalPolicies
> import DynamicProgrammingSmall.S1304_MaxArgmax
> import DynamicProgrammingSmall.S1305_BackwardsInduction
> import DynamicProgrammingSmall.S1307_FiniteState


> %default total

> tabulatedOptExtension :
>   (t : Nat) -> 
>   (n : Nat) -> 
>   Vect (nX (S t) n) Float ->
>   Policy t (S n)
> tabulatedOptExtension t n' vt = p where
>   p : Policy t (S n')
>   p x r v = yq where 
>     yq : (y : Y t x ** So (feasible n' x y))
>     yq = argmax n' x r v f where
>       f : (y' : Y t x ** So (feasible n' x y')) -> Float
>       f yq' = meas (Mmap (f' yq') (step t x (outl yq'))) where
>         f' : (y : Y t x ** So (feasible n' x y)) -> X (S t) -> Float  
>         f' yq'' x' = reward t x y x' + idx vt i' where
>           y : Y t x
>           y = outl yq''
>           mx' : M (X (S t))
>           mx' = step t x y
>           postulate x'ins : So (x' `MisIn` mx')
>           r' : So (reachable x')
>           r' = reachableSpec1 x r y x' x'ins
>           v' : So (viable n' x')
>           v' = Mspec2 mx' (viable n') (outr yq'') x' x'ins
>           xrv' : (x'' : X (S t) **
>                  (So (reachable x''), So (viable n' x'')))
>           xrv' = (x' ** (r', v'))
>           i' : Blt (nX (S t) n')
>           i' = index n' xrv'

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
> tbi t m c clten ps vt =
>   if (c == m) 
>   then believe_me ps
>   else tbi t m c' c'lten ps' vvt' where
>     cltmpn : So (c < t + m)
>     cltmpn = believe_me Oh
>     c' : Nat
>     c' = S c
>     t' : Nat
>     t' = t + m - c'
>     c'lten : So (c' <= m)
>     c'lten = believe_me Oh
>     p : Policy t' c'
>     p = tabulatedOptExtension t' c (castvt (t + m) c c vt (believe_me Oh))
>     ps' : PolicySeq t' c'
>     ps' = (p :: (castPolicySeq (t + m) c c ps cltmpn))
>     vvt' : Vect (nX t' c') Float
>     vvt' = toVect vt' where
>       vt' : Blt (nX t' c') -> Float
>       vt' i = meas (Mmap f mx') where          
>         xrv : (w : X t' ** (So (reachable w), So (viable c' w)))
>         xrv = xedni c' i
>         x : X t'
>         x = outl xrv
>         rv : (So (reachable x), So (viable c' x))
>         rv = outr xrv
>         r : So (reachable x)
>         r = fst rv
>         v : So (viable c' x)
>         v = snd rv
>         y : Y t' x
>         y = outl (p x r v)
>         mx' : M (X (S t'))
>         mx' = step t' x y
>         vt'' : Vect (nX (S (t + m - c')) c) Float
>         vt'' = castvt (t + m) c c vt (believe_me Oh)
>         f : X (S t') -> Float
>         f x' = reward t' x y x' + idx vt'' i' where
>           r' : So (reachable x')
>           r' = reachableSpec1 x r y x' (believe_me Oh)
>           v' : So (viable c x')  
>           v' = Mspec2 mx' (viable c) (outr (p x r v)) x' (believe_me Oh)
>           i' : Blt (nX (S t') c)
>           i' = index c (x' ** (r',v'))

> tabulatedBackwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n
> tabulatedBackwardsInduction t n = tbi t n Z lemma1 Nil (toVect (\ i => 0))

