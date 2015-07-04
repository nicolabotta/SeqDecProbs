> module BackwardsInduction

> import Data.So

> import Float.Postulates

> import DynamicProgrammingSmall.S1301_Context
> import DynamicProgrammingSmall.S1302_Reachability
> import DynamicProgrammingSmall.S1302_Viability
> import DynamicProgrammingSmall.S1302_Feasibility
> import DynamicProgrammingSmall.S1303_OptimalPolicies
> import DynamicProgrammingSmall.S1304_MaxArgmax

> optExtension : (t : Nat) -> 
>                (n : Nat) -> 
>                PolicySeq (S t) n -> 
>                Policy t (S n)

> optExtension t n ps = p where
>   p : Policy t (S n)
>   p x r v = yq where 
>     yq : (y : Y t x ** So (feasible n x y))
>     yq = argmax n x r v f where
>       f' : (y : Y t x ** So (feasible n x y)) -> X (S t) -> Float
>       f' ycy x' = reward t x y x' + Val (S t) n x' r' v' ps where
>         y : Y t x
>         y = getWitness ycy
>         postulate x'ins : So (x' `MisIn` (step t x y))
>         r' : So (reachable x')
>         r' = reachableSpec1 x r y x' x'ins
>         v' : So (viable n x')
>         v' = Mspec2 (step t x y) (viable n) (getProof ycy) x' x'ins
>       f : (y : Y t x ** So (feasible n x y)) -> Float
>       f ycy = meas (Mmap (f' ycy) (step t x (getWitness ycy)))

> backwardsInduction : (t : Nat) -> (n : Nat) -> PolicySeq t n

> backwardsInduction _ Z = Nil

> backwardsInduction t (S n) = ((optExtension t n ps) :: ps) where
>   ps : PolicySeq (S t) n
>   ps = backwardsInduction (S t) n




