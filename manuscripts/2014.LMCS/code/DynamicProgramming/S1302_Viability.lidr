> module Viability

> import Data.So

> import Util.VectExtensions1
> import DynamicProgramming.S1301_Context

> %default total


> viable       :  (n : Nat) -> X t -> Bool

> Viable       :  (n : Nat) -> X t -> Type
> Viable n x = So (viable n x)

> feasible            :  (n : Nat) -> (x : X t) -> Y t x -> Bool
> feasible {t} n x y  =  MareAllTrue (Mmap (viable n) (step t x y))

> Feasible            :  (n : Nat) -> (x : X t) -> Y t x -> Type
> Feasible n x y = So (feasible n x y)

> YF : (t : Nat) -> (n : Nat) -> X t -> Type
> YF t n x = (y : Y t x ** Feasible n x y)

> viableSpec0  :  (x : X t) -> Viable Z x
> viableSpec1  :  (x : X t) -> Viable (S n) x -> YF t n x
> viableSpec2  :  (x : X t) -> YF t n x -> Viable (S n) x
