> module Viability


> import Util.VectExtensions1
> import DynamicProgramming.S1301_Context

> %default total


> viable       :  (n : Nat) -> X t -> Bool

> Viable       :  (n : Nat) -> X t -> Type
> Viable n x = so (viable n x)

> Mfeasible            :  (n : Nat) -> (x : X t) -> Y t x -> Bool
> Mfeasible {t} n x y  =  MareAllTrue (Mmap (viable n) (step t x y)) 

> MFeasible            :  (n : Nat) -> (x : X t) -> Y t x -> Type
> MFeasible n x y = so (Mfeasible n x y)

> YF : (t : Nat) -> (n : Nat) -> X t -> Type
> YF t n x = (y : Y t x ** MFeasible n x y)

> viableSpec0  :  (x : X t) -> Viable Z x
> viableSpec1  :  (x : X t) -> Viable (S n) x -> YF t n x
> viableSpec2  :  (x : X t) -> YF t n x -> Viable (S n) x

