> module OptimalPolicies

> import Data.So

> import Float.Properties

> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1302_Viability
> import DynamicProgramming.S1302_Feasibility

> %default total


> Policy : Nat -> Nat -> Type
> Policy t Z = Void
> Policy t (S n) = (x : X t) -> 
>                  (r : So (reachable x)) -> 
>                  (v : So (viable (S n) x)) -> 
>                  (y : Y t x ** So (feasible n x y))
 

> data PolicySeq : Nat -> Nat -> Type where
>   Nil : PolicySeq t Z
>   (::) : Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)


> Val : (t : Nat) ->
>       (n : Nat) ->
>       (x : X t) -> 
>       (r : So (reachable x)) -> 
>       (v : So (viable n x)) -> 
>       PolicySeq t n -> 
>       Float
> Val _ Z _ _ _ _ = 0
> Val t (S n) x r v (p :: ps) = meas (Mmap f mx') where
>   y : Y t x
>   y = getWitness (p x r v)
>   mx' : M (X (S t))
>   mx' = step t x y
>   f : X (S t) -> Float
>   f x' = reward t x y x' + Val (S t) n x' r' v' ps where
>     postulate x'ins : So (x' `MisIn` mx')
>     r' : So (reachable x')
>     r' = reachableSpec1 x r y x' x'ins
>     v' : So (viable n x')
>     v' = Mspec2 mx' (viable n) (getProof (p x r v)) x' x'ins

-- > mutual

-- >   Val : (t : Nat) ->
-- >         (n : Nat) ->
-- >         (x : X t) -> 
-- >         (r : So (reachable x)) -> 
-- >         (v : So (viable n x)) -> 
-- >         PolicySeq t n -> 
-- >         Float
-- >   Val _ Z _ _ _ _ = 0
-- >   Val t (S n) x r v (p :: ps) = meas (Mmap f mx') where
-- >     y : Y t x
-- >     y = getWitness (p x r v)
-- >     mx' : M (X (S t))
-- >     mx' = step t x y
-- >     f : X (S t) -> Float
-- >     f = val t n x r v p ps

-- >   val : (t : Nat) ->
-- >         (n : Nat) ->
-- >         (x : X t) -> 
-- >         (r : So (reachable x)) -> 
-- >         (v : So (viable (S n) x)) -> 
-- >         Policy t (S n) ->
-- >         PolicySeq (S t) n -> 
-- >         X (S t) -> 
-- >         Float
-- >   val t n x r v p ps x' = 
-- >     reward t x y x' + Val (S t) n x' r' v' ps where
-- >       y : Y t x
-- >       y = getWitness (p x r v)
-- >       mx' : M (X (S t))
-- >       mx' = step t x y  
-- >       postulate x'ins : So (x' `MisIn` mx')
-- >       r' : So (reachable x')
-- >       r' = reachability1 x r y x' x'ins
-- >       v' : So (viable n x')
-- >       v' = Mspec2 mx' (viable n) (getProof (p x r v)) x' x'ins


The notion of optimal sequence of policies

> OptPolicySeq : (t : Nat) -> (n : Nat) -> PolicySeq t n -> Type
> OptPolicySeq t n ps = (ps' : PolicySeq t n) -> 
>                       (x : X t) ->
>                       (r : So (reachable x)) -> 
>                       (v : So (viable n x)) -> 
>                       So (Val t n x r v ps' <= Val t n x r v ps)

Sanity check: Nil is optimal policy sequence                             

> nilIsOptPolicySeq : OptPolicySeq t Z Nil
> nilIsOptPolicySeq _ _ _ _ = reflexive_Float_lte 0

