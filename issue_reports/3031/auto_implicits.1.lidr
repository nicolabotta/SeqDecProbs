> module Test
> import Data.So

> %default total
> -- %auto_implicits off

> Blt : Nat -> Type
> Blt b = (n : Nat ** LT n b)

> nColumns : Nat
> nColumns = 5

> valid : Nat -> Blt nColumns -> Bool
> valid t i with (decEq t 3)
>   | (Yes _) = fst i > 3
>   | (No  _) = True

> State : Nat -> Type
> State t = (i : Blt nColumns ** So (valid t i))

> column : {t : Nat} -> State t -> Nat
> column x = fst (fst x)

> foo : {t : Nat} -> (n : Nat) -> State t -> Bool
> foo {t} n x =
>   (n == Z)
>   ||
>   (n == 1 && not (t == 2 && column x < 3))
>   ||
>   (n == 2 && not ((t == 2 && column x < 3)
>                   ||
>                   (t == 1 && column x < 2)))
>   ||
>   (n >= 3 && not ((t == 2 && column x < 3)
>                   ||
>                   (t == 1 && column x < 2)
>                   ||
>                   (t == 0 && column x < 1)))

> nSteps : Nat
> nSteps = 4
 
> x0 : State Z
> x0 = ((1 ** LTESucc (LTESucc LTEZero)) ** Oh)

 
> v0 : So (foo {t = Z} nSteps x0)
> v0 = Oh
 
