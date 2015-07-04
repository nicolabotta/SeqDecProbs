> module Viability

> import Data.So

> import Util.VectExtensions1

> import DynamicProgrammingSmall.S1301_Context

> %default total
  

> viable : (n : Nat) -> X t -> Bool

> viableSpec0 : (x : X t) -> So (viable Z x)

> viableSpec1 : 
>   (x : X t) -> 
>   So (viable (S n) x) -> 
>   -- (y : Y t x ** So (x' `MisIn` (step t x y)) -> So (viable n x'))
>   (y : Y t x ** So (MareAllTrue (Mmap (viable n) (step t x y))))

> viableSpec2 : 
>   (x : X t) -> 
>   -- (y : Y t x ** So (x' `MisIn` (step t x y)) -> So (viable n x')) -> 
>   (y : Y t x ** So (MareAllTrue (Mmap (viable n) (step t x y)))) ->
>   So (viable (S n) x)
