> module Main


> import BoundedNat.Blt


A simple numerical experiment with |S115_Example1| suggests that the
computational cost of |backwardsInduction| grows exponentially in the
number of steps:

n         t  ln (t_{k+1} / t_{k}) / (n_{k+1} - n_{k})
2     0.004  
3     0.028  1.94
4     0.348  2.52
5     3.560  2.32
6    35.398  2.29
7   370.227  2.35
8  3621.786  2.28

On the other hand, straightworward counting the number of evaluations of
|step| and |reward| required by |backwardsInduction| 

> cX : Float
> cX = 5

> cY : Float
> cY = 3

> costReward : Float
> costReward = 1

> costStep : Float
> costStep = 1

-- > Val : (x : X) -> PolicySeq n -> Float
-- > Val {n = O} _ _ = 0
-- > Val {n = S m} x (p :: ps) = reward x (p x) x' + Val x' ps where
-- >   x' : X  
-- >   x' = step x (p x)

> costVal : Nat -> Float
> costVal O = 0
> costVal (S n) = costReward + costStep + costVal n

-- > optExtension : PolicySeq n -> Policy
-- > optExtension ps x = argmax x f where
-- >   f : Y x -> Float  
-- >   f y = reward x y x' + Val x' ps where
-- >     x' : X
-- >     x' = step x y

> costOptExtension : (n : Nat) -> Float
> costOptExtension O = costReward + costStep
> costOptExtension (S n) = cX * costArgmax where
>   costArgmax : Float  
>   costArgmax = cY  * (costReward + costStep + costVal (S n))

-- > backwardsInduction : (n : Nat) -> PolicySeq n
-- > backwardsInduction O = Nil
-- > backwardsInduction (S n) = ((optExtension ps) :: ps) where
-- >   ps : PolicySeq n
-- >   ps = backwardsInduction n
         
> costBackwardsInduction : (n : Nat) -> Float
> costBackwardsInduction O = 0
> costBackwardsInduction (S n) = 
>   costOptExtension n + costBackwardsInduction n

suggests quadratic cost in the number of steps (|t_k =
costBackwardsInduction n_k|):

  n      t  ln (t_{k+1} / t_{k}) / ln (n_{k+1} / n_{k})
  2      6  
  3     12  1.71
  4     20  1.77
  5     30  1.82
  6     42  1.84
  7     56  1.87
  8     72  1.88
 16    272  1.92
 32   1056  1.96
 64   4160  1.98
128  16512  1.99

Notice that the computational cost of |backwardsInduction| can be made
linear in the number of time steps by replacing the recursion in |Val|
with an iteration (and an accumulator).

Thus, the problem of deriving an efficient implementation of
|backwardsInduction| consists of two steps: 1) achieve quadratic
complexity in the original algorithm and 2) replace recursion in |Val|
with iteration. We treat these two problems separately.

