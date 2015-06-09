> module OptimalControls

> import Data.So

> import Float.Properties
> import DynamicProgramming.S1101_Context

> %default total


> data CtrlSeq : State -> Nat -> Type where
>   Nil   :  CtrlSeq x Z
>   (::)  :  (y : Ctrl x) -> CtrlSeq (step x y) n -> CtrlSeq x (S n)

> value : {x : State} -> {n : Nat} -> CtrlSeq x n -> Float
> value      {n = Z}    _          =  0
> value {x}  {n = S m}  (y :: ys)  =  reward x y (step x y) + value ys

> OptCtrlSeq : {x : State} -> {n : Nat} -> CtrlSeq x n -> Type
> OptCtrlSeq {x} {n} ys = (ys' : CtrlSeq x n) -> So (value ys' <= value ys)

> nilIsOptCtrlSeq : (x : State) -> OptCtrlSeq {x} Nil
> nilIsOptCtrlSeq x ys' = reflexive_Float_lte 0
