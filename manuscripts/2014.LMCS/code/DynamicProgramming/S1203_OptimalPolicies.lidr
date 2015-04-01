> module OptimalPolicies


> import Float.Properties
> import Exists.Ops

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability
> import DynamicProgramming.S1203_OptimalControls


> %default total


It is easy to compute sequences of feasible controls if one has a rule
that tells one which control to select when in a given state. Such rules
are called policies

> Policy : Nat -> Nat -> Type
> Policy t Z      =  ()
> Policy t (S n)  =  (x : X t) -> Reachable x -> Viable (S n) x -> YV t n x

At time |t|, a policy which grants |S n| further steps associates to
every |x : X t| which is reachable and viable for |S n| steps a control
yielding a state which is viable (at least) |n| steps.  The existence of
such a control is granted by the first viability theorem |viability1|,
see S1202_reachabilityViability.lidr.

While viability is necessary to grant further steps, reachability is
used to restrict the set of states for which (optimal) controls have to
be computed in backwards induction algorithms. In cases in which |X t|
is large but only few states are reachable at a given time, this can
significantly improve the computational efficiency.

Sequences of policies can be represented by values of type:

> data PolicySeq : Nat -> Nat -> Type where
>   Nil   :  PolicySeq t Z
>   (::)  :  Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)

Given one such sequences, the corresponding sequence of controls is

> ctrl : (x : X t) ->
>        (n : Nat) -> 
>        (r : so (reachable x)) -> 
>        (v : so (viable n x)) -> 
>        PolicySeq t n -> 
>        CtrlSeq x n

> ctrl _ _ _ _ Nil = Nil

> ctrl {t} x (S n) r v (p :: ps) = (yv :: ctrl {t = S t} x' n r' v' ps) where
>   yv : (y : Y t x ** so (viable {t = S t} n (step t x y)))
>   yv = p x r v
>   x' : X (S t)
>   x' = step t x (outl yv)
>   r' : so (reachable {t = S t} x')
>   r' = reachableSpec1 x r (outl yv)
>   v' : so (viable {t = S t} n x')
>   v' = outr yv

...

> Val : (t : Nat) ->
>       (n : Nat) ->
>       (x : X t) -> 
>       (r : Reachable x) -> 
>       (v : Viable n x) -> 
>       PolicySeq t n -> 
>       Float
> Val _ Z _ _ _ _ = 0
> Val t (S n) x r v (p :: ps) = reward t x y x' + Val (S t) n x' r' v' ps where
>   y : Y t x;;           x' : X (S t)
>   y = outl (p x r v);;  x' = step t x y
>   r' : Reachable {t = S t} x';
>   r' = reachableSpec1 x r y;
>   v' : Viable {t = S t} n x';
>   v' = outr(p x r v)

The notion of optimal sequence of policies

> OptPolicySeq : (t : Nat) -> (n : Nat) -> PolicySeq t n -> Type
> OptPolicySeq t n ps = (ps' : PolicySeq t n) -> 
>                       (x : X t) ->
>                       (r : so (reachable x)) -> 
>                       (v : so (viable n x)) -> 
>                       so (Val t n x r v ps' <= Val t n x r v ps)

(Sanity check: Nil is optimal policy sequence                             

> nilIsOptPolicySeq : OptPolicySeq t Z Nil
> nilIsOptPolicySeq _ _ _ _ = reflexive_Float_lte 0

) is interesting because of the following lemma

> OptLemma :   (n : Nat) -> 
>              (ps : PolicySeq t n) ->                                                                   
>              OptPolicySeq t n ps ->
>              (x : X t) ->
>              (r : so (reachable x)) -> 
>              (v : so (viable n x)) -> 
>              OptCtrlSeq x n (ctrl x n r v ps)
                                                                
> -- OptLemma Z Nil _ x r (viableSpec0 x) = nilIsOptCtrlSeq x
> OptLemma Z Nil _ x _ _  = nilIsOptCtrlSeq x

> OptLemma (S n) (p :: ps) opt_pps x rx vx = believe_me oh




