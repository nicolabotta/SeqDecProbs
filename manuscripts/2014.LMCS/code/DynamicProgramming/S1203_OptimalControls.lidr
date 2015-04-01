> module OptimalControls


> import Float.Properties
> import Exists.Ops

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability


> %default total


Sequences of feasible controls of length |n| starting in |x : X t| can
be represented by values of type

> data CtrlSeq : (x : X t) -> (n : Nat) -> Type where
>   Nil   :  CtrlSeq {t} x Z
>   (::)  :  {x : X t} -> 
>            -- (yv : (y : Y t x ** Viable {t = S t} n (step t x y))) -> 
>            (yv : YV t n x ) -> 
>            CtrlSeq (step t x (outl yv)) n ->
>            CtrlSeq x (S n)

For such sequences to exist, |x| is required to be viable (at least) |n|
steps. The first control of a sequence of length |S n| is required to
yield a state which is viable |n| steps. The existence of such a control
is granted by the first viability theorem |viability1|, see
S1202_reachabilityViability.lidr. Similarly for the second, third,
etc. control. The last control is required to yield a state which is
viable |0| steps. This holds, per definition, for every feasible control.

The sum of the rewards obtained in |n| steps when starting in |x| is

> val  :  (x : X t) -> (n : Nat) -> CtrlSeq x n -> Float
> val _ Z _                   =  0
> val {t} x (S n) (yv :: ys)  =  reward t x y x' + val x' n ys where
>   y   :  Y t x;;      x'  :  X (S t)
>   y   =  outl yv;;    x'  =  step t x y

A sequence of |n| feasible controls is optimal when starting in |x| if no
other sequence of feasible controls of the same length yield a better
|val| when starting in the same |x|:

> OptCtrlSeq : (x : X t) -> (n : Nat) -> CtrlSeq x n -> Type
> OptCtrlSeq x n ys = (ys' : CtrlSeq x n) -> so (val x n ys' <= val x n ys)

Sanity check: |Nil| is optimal control sequence

> nilIsOptCtrlSeq        :  (x : X t) -> OptCtrlSeq x Z Nil
> nilIsOptCtrlSeq x Nil  =  reflexive_Float_lte 0

