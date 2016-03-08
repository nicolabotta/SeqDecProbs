> module OptimalPolicies

> import Data.So

> import Exists.Ops
> import Double.Properties
> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1302_Viability


> Policy : Nat -> Nat -> Type
> Policy t Z = ()
> Policy t (S n) = (x : State t) -> Reachable x -> Viable (S n) x -> GoodCtrl t n x

> data PolicySeq : Nat -> Nat -> Type where
>   Nil   : PolicySeq t Z
>   (::)  : Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)

> Mval  :  (t : Nat) -> (n : Nat) ->
>          (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>          PolicySeq t n -> Double
> Mval _  Z      _  _  _  _          =  0
> Mval t  (S n)  x  r  v  (p :: ps)  =  Mmeas (Mmap f (toSub mx')) where
>   y    :  Ctrl t x;;          y    =  outl (p x r v)
>   mx'  :  M (State (S t));;   mx'  =  step t x y
>   f : (x' : State (S t) ** So (x' `MisIn` mx')) -> Double
>   f (x' ** x'ins) =  reward t x y x' + Mval (S t) n x' r' v' ps where
>     r'  :  Reachable x';;   r'  =  reachableSpec1 x r y x' x'ins
>     v'  :  Viable n x';;    v'  =  Mspec2 mx' (viable n) (outr (p x r v)) x' x'ins

> OptPolicySeq : (t : Nat) -> (n : Nat) -> PolicySeq t n -> Type
> OptPolicySeq t n ps = (ps' : PolicySeq t n) ->
>                       (x : State t) ->
>                       (r : Reachable x) ->
>                       (v : Viable n x) ->
>                       So (Mval t n x r v ps' <= Mval t n x r v ps)

> nilIsOptPolicySeq : OptPolicySeq t Z Nil
> nilIsOptPolicySeq _ _ _ _ = reflexive_Double_lte 0
