> module Viability

> import Data.So

> import Util.VectExtensions1
> import DynamicProgramming.S1301_Context

> %default total


> viable       :  (n : Nat) -> State t -> Bool

> Viable       :  (n : Nat) -> State t -> Type
> Viable n x = So (viable n x)

> Mfeasible            :  (n : Nat) -> (x : State t) -> Ctrl t x -> Bool
> Mfeasible {t} n x y  =  MareAllTrue (Mmap (viable n) (step t x y))

> MFeasible            :  (n : Nat) -> (x : State t) -> Ctrl t x -> Type
> MFeasible n x y = So (Mfeasible n x y)

> CtrlF : (t : Nat) -> (n : Nat) -> State t -> Type
> CtrlF t n x = (y : Ctrl t x ** MFeasible n x y)

> viableSpec0  :  (x : State t) -> Viable Z x
> viableSpec1  :  (x : State t) -> Viable (S n) x -> CtrlF t n x
> viableSpec2  :  (x : State t) -> CtrlF t n x -> Viable (S n) x
