> module OptimalPolicies

> import Data.So

> import Float.Properties
> import Exists.Ops

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability
> import DynamicProgramming.S1203_OptimalControls


> %default total


> Policy : Nat -> Nat -> Type
> Policy t Z      =  ()
> Policy t (S n)  =  (x : State t) -> Reachable x -> Viable (S n) x -> GoodCtrl t n x

> data PolicySeq : Nat -> Nat -> Type where
>   Nil   :  PolicySeq t Z
>   (::)  :  Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)

> ctrl : (x : State t) ->
>        (n : Nat) -> 
>        (r : So (reachable x)) -> 
>        (v : So (viable n x)) -> 
>        PolicySeq t n -> 
>        CtrlSeq x n

> ctrl _ _ _ _ Nil = Nil

> ctrl {t} x (S n) r v (p :: ps) = (yv :: ctrl {t = S t} x' n r' v' ps) where
>   yv : (y : Ctrl t x ** So (viable {t = S t} n (step t x y)))
>   yv = p x r v
>   x' : State (S t)
>   x' = step t x (outl yv)
>   r' : So (reachable {t = S t} x')
>   r' = reachableSpec1 x r (outl yv)
>   v' : So (viable {t = S t} n x')
>   v' = outr yv

...

> Val : (t : Nat) ->
>       (n : Nat) ->
>       (x : State t) -> 
>       (r : Reachable x) -> 
>       (v : Viable n x) -> 
>       PolicySeq t n -> 
>       Float
> Val _ Z _ _ _ _ = 0
> Val t (S n) x r v (p :: ps) = reward t x y x' + Val (S t) n x' r' v' ps where
>   y : Ctrl t x;;           x' : State (S t)
>   y = outl (p x r v);;  x' = step t x y
>   r' : Reachable {t = S t} x';
>   r' = reachableSpec1 x r y;
>   v' : Viable {t = S t} n x';
>   v' = outr(p x r v)

The notion of optimal sequence of policies

> OptPolicySeq : (t : Nat) -> (n : Nat) -> PolicySeq t n -> Type
> OptPolicySeq t n ps = (ps' : PolicySeq t n) -> 
>                       (x : State t) ->
>                       (r : So (reachable x)) -> 
>                       (v : So (viable n x)) -> 
>                       So (Val t n x r v ps' <= Val t n x r v ps)

(Sanity check: Nil is optimal policy sequence                             

> nilIsOptPolicySeq : OptPolicySeq t Z Nil
> nilIsOptPolicySeq _ _ _ _ = reflexive_Float_lte 0

) is interesting because of the following lemma

> OptLemma :   (n : Nat) -> 
>              (ps : PolicySeq t n) ->                                                                   
>              OptPolicySeq t n ps ->
>              (x : State t) ->
>              (r : So (reachable x)) -> 
>              (v : So (viable n x)) -> 
>              OptCtrlSeq x n (ctrl x n r v ps)
                                                                
> -- OptLemma Z Nil _ x r (viableSpec0 x) = nilIsOptCtrlSeq x
> OptLemma Z Nil _ x _ _  = nilIsOptCtrlSeq x

> OptLemma (S n) (p :: ps) opt_pps x rx vx = believe_me Oh




