> import Data.So

> %default total
> -- %auto_implicits off

> Foo : Nat -> Type
> Foo b = (n : Nat ** LT n b)

> foo : Nat -> Foo 5 -> Bool
> foo t i with (decEq t 3)
>   | (Yes _) = fst i > 3
>   | (No  _) = True

> Bar : Nat -> Type
> Bar t = (i : Foo 5 ** So (foo t i))

> bar : {t : Nat} -> (n : Nat) -> Bar t -> Bool
> bar {t} n x =
>   (n == Z)
>   ||
>   (n == 1 && not ( t == 2 && fst (fst x) < 3))
>   ||
>   (n == 2 && not ((t == 2 && fst (fst x) < 3)
>                   ||
>                   (t == 1 && fst (fst x) < 2)))
>   ||
>   (n >= 3 && not ((t == 2 && fst (fst x) < 3)
>                   ||
>                   (t == 1 && fst (fst x) < 2)
>                   ||
>                   (t == 0 && fst (fst x) < 1)))

> x0 : Bar Z
> x0 = ((1 ** LTESucc (LTESucc LTEZero)) ** Oh)
 
> v0 : So (bar {t = Z} 4 x0)
> v0 = Oh
 
