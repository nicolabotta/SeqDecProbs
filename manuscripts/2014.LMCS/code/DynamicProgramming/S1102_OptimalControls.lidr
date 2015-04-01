> module OptimalControls

> import Float.Properties
> import DynamicProgramming.S1101_Context

> %default total

Sequences of feasible controls can be represented by values of type

-- > CtrlSeq : X -> Nat -> Type
-- > CtrlSeq _ Z = ()
-- > CtrlSeq x (S n) = (y : Y x ** CtrlSeq (step x y) n)

> data CtrlSeq : X -> Nat -> Type where
>   Nil   :  CtrlSeq x Z
>   (::)  :  (y : Y x) -> CtrlSeq (step x y) n -> CtrlSeq x (S n)

The sum of the rewards obtained in n steps when starting in x is

-- > val : (x : X) -> (n : Nat) -> CtrlSeq x n -> Float
-- > val _ Z _ = 0
-- > val x (S n) (y ** ys) = reward x y x' + val x' n ys where
-- >   x' : X  
-- >   x' = step x y

> val : CtrlSeq x n -> Float
> -- val Nil = 0
> -- val {x} (y :: ys) = reward x y (step x y) + val ys
> val     {n = Z} _ = 0
> val {x} {n = S m} (y :: ys) = reward x y (step x y) + val ys

A sequence of n feasible controls is optimal when starting in x if no
other sequence of feasible controls of the same length yield a better
val when starting in the same x:

-- > OptCtrlSeq : (x : X) -> (n : Nat) -> CtrlSeq x n -> Type
-- > OptCtrlSeq x n ys = (ys' : CtrlSeq x n) -> so (val x n ys' <= val x n ys)

> OptCtrlSeq : CtrlSeq x n -> Type
> OptCtrlSeq {x} {n} ys = (ys' : CtrlSeq x n) -> so (val ys' <= val ys)

Sanity check: () is optimal control sequence

-- > oneIsOptCtrlSeq : (x : X) -> OptCtrlSeq x Z ()
-- > oneIsOptCtrlSeq x () = reflexive_Float_lte 0

> nilIsOptCtrlSeq : (x : X) -> OptCtrlSeq {x} Nil
> nilIsOptCtrlSeq x ys' = reflexive_Float_lte 0


