> module OptimalPolicies

> import Data.So

> import Exists.Ops
> import Float.Properties
> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1302_Viability


> Policy : Nat -> Nat -> Type
> Policy t Z = ()
> Policy t (S n) = (x : X t) -> Reachable x -> Viable (S n) x -> YF t n x
 

> data PolicySeq : Nat -> Nat -> Type where
>   Nil   : PolicySeq t Z
>   (::)  : Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)


> MVal  :  (t : Nat) -> (n : Nat) ->
>          (x : X t) -> (r : Reachable x) -> (v : Viable n x) -> 
>          PolicySeq t n -> Float
> MVal _  Z      _  _  _  _          = 0
> MVal t  (S n)  x  r  v  (p :: ps)  = Mmeas (Mmap f (toSub mx')) where
>   y     :  Y t x
>   y     =  getWitness (p x r v)
>   mx'   :  M (X (S t))
>   mx'   =  step t x y
>   f     :  (x' : X (S t) ** So (x' `MisIn` mx')) -> Float
>   f (x' ** x'ins) =  reward t x y x' + MVal (S t) n x' r' v' ps where
>     r'  :  Reachable x'
>     r'  =  reachableSpec1 x r y x' x'ins
>     v'  :  Viable n x'
>     v'  =  Mspec2 mx' (viable n) (getProof (p x r v)) x' x'ins

> {-
> -- MVal t (S n) x r v (p :: ps) = Mmeas (Mmap f mx') where
>   f x'  =  reward t x y x' + MVal (S t) n x' r' v' ps where
>     postulate x'ins : So (x' `MisIn` mx')
>     r'  :  So (reachable x')
>     r'  =  reachableSpec1 x r y x' x'ins
>     v'  :  So (viable n x')
>     v' = Mspec2 mx' (viable n) (getProof (p x r v)) x' x'ins
> -}

> {-
>   f x' with (soIntro (reachable x'))
>     | (Yes r') with (soIntro (viable n x'))
>         | (Yes v') = reward t x y x' + MVal (S t) n x' r' v' ps
>         | (No _)  = reward t x y x'
>     | (No _) = reward t x y x'
> -}

The notion of optimal sequence of policies

> OptPolicySeq : (t : Nat) -> (n : Nat) -> PolicySeq t n -> Type
> OptPolicySeq t n ps = (ps' : PolicySeq t n) -> 
>                       (x : X t) ->
>                       (r : So (reachable x)) -> 
>                       (v : So (viable n x)) -> 
>                       So (MVal t n x r v ps' <= MVal t n x r v ps)

Sanity check: Nil is optimal policy sequence                             

> nilIsOptPolicySeq : OptPolicySeq t Z Nil
> nilIsOptPolicySeq _ _ _ _ = reflexive_Float_lte 0

