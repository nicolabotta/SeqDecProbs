> module Trajectories

> import Data.So

> import DynamicProgrammingSmall.S1301_Context
> import DynamicProgrammingSmall.S1302_Reachability
> import DynamicProgrammingSmall.S1302_Viability
> import DynamicProgrammingSmall.S1303_OptimalPolicies

> %default total


> data StateCtrlSeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil : (x : X t) -> StateCtrlSeq t Z
>   (::) : (x : X t ** Y t x) -> 
>          StateCtrlSeq (S t) n -> 
>          StateCtrlSeq t (S n) 

> stateCtrlTrj : (t : Nat) -> 
>                (n : Nat) ->
>                (x : X t) ->
>                (r : So (reachable x)) -> 
>                (v : So (viable n x)) -> 
>                (ps : PolicySeq t n) ->
>                M (StateCtrlSeq t n)

> stateCtrlTrj _ Z x _ _ _ = Mret (Nil x)

> stateCtrlTrj t (S n) x r v (p :: ps') = 
>   -- Mmap ((::) (x ** y)) (Mbind {alpha = X (S t)} {beta = StateCtrlSeq (S t) n} mx' f) where
>   -- Mmap ((::) (x ** y)) (mx' `Mbind` f) where
>   Mmap g (mx' `Mbind` f) where  
>     y : Y t x
>     y = getWitness (p x r v)
>     g : StateCtrlSeq (S t) n -> StateCtrlSeq t (S n) 
>     g xys = (x ** y) :: xys
>     mx' : M (X (S t))
>     mx' = step t x y
>     f : X (S t) -> M (StateCtrlSeq (S t) n)
>     f x' = stateCtrlTrj (S t) n x' r' v' ps' where
>       postulate x'inmx' : So (x' `MisIn` mx')
>       r' : So (reachable x')
>       r' = reachableSpec1 x r y x' x'inmx'
>       v' : So (viable n x')
>       v' = Mspec2 mx' (viable n) (getProof (p x r v)) x' x'inmx'


