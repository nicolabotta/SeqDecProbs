> module Trajectories

> import Exists.Ops

> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1303_OptimalPolicies


> data StateCtrlSeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  (x : X t) -> StateCtrlSeq t Z
>   (::)  :  (x : X t ** Y t x) -> 
>            StateCtrlSeq (S t) n -> 
>            StateCtrlSeq t (S n) 

> stateCtrlTrj  :  (t : Nat) -> (n : Nat) ->
>                  (x : X t) -> (r : Reachable x) -> (v : Viable n x) -> 
>                  (ps : PolicySeq t n) -> M (StateCtrlSeq t n)
> stateCtrlTrj _  Z      x  _  _  _           = Mret (Nil x)
> stateCtrlTrj t  (S n)  x  r  v  (p :: ps')  = Mmap prepend (toSub mx' `Mbind` f) where  
>   y : Y t x
>   y = getWitness (p x r v)
>   prepend : StateCtrlSeq (S t) n -> StateCtrlSeq t (S n) 
>   prepend xys = (x ** y) :: xys
>   mx' : M (X (S t))
>   mx' = step t x y
>   f : (x' : X (S t) ** so (x' `MisIn` mx')) -> M (StateCtrlSeq (S t) n)
>   f (x' ** x'inmx') = stateCtrlTrj (S t) n x' r' v' ps' where
>     r' : Reachable x'
>     r' = reachableSpec1 x r y x' x'inmx'
>     v' : Viable n x'
>     v' = Mspec2 mx' (viable n) (getProof (p x r v)) x' x'inmx'

> {-
>   Mmap ((::) (x ** y)) (mx' `Mbind` f) where
>     y    :  Y t x
>     y    =  outl (p x r v)
>     mx'  :  M (X (S t))
>     mx'  =  step t x y
>     f     :  X (S t) -> M (StateCtrlSeq (S t) n)
>     f x'  =  stateCtrlTrj (S t) n x' r' v' ps' where
>       postulate x'inmx' : so (x' `MisIn` mx')
>       r'  :  so (reachable x')
>       r'  =  reachableSpec1 x r y x' x'inmx'
>       v'  :  so (viable n x')
>       v'  =  MisInMareAllTrueSpec mx' (viable n) (getProof (p x r v)) x' x'inmx'
> -}

