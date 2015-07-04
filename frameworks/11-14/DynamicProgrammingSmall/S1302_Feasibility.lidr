> module Feasibility

> import Data.So

> import DynamicProgrammingSmall.S1301_Context
> import DynamicProgrammingSmall.S1302_Viability

> %default total


> feasible : (n : Nat) -> (x : X t) -> Y t x -> Bool
> feasible {t} n x y = MareAllTrue (Mmap (viable n) (step t x y))

First viability theorem, motivated by the implementation of yfysP, 

> viability1 : (x : X t) -> 
>              So (viable (S n) x) -> 
>              (y : Y t x ** So (feasible n x y))

The idea is:

viable (S n) x
  = {def.}
isAnyBy (\ mx => MareAllTrue (Mmap (viable n) mx)) (succs x)  
  => {lemma3'}
(mx' : M (X (S t)) ** mx' `isIn` (succs x) && MareAllTrue (Mmap (viable n) mx'))
  => {lemmaSuccs2}
(y : Y t x ** mx' = step t x y)
  => {def. feasible n x y}
(y : Y t x ** feasible n x y)

> viability1 x v = believe_me Oh 


