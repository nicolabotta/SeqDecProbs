> module Main

> import Util.VectExtensions1

-- test:

> m : Nat
> m = 10

> n : Nat
> n = m + 800

> lnats : List Nat
> lnats = [1..n]

> vnats : Vect Nat n
> vnats = fromList lnats

> lmats : List Nat
> lmats = [1..m]

> vmats : Vect Nat m
> vmats = fromList lmats

-- > fvmats : Vect Nat m
-- > fvmats = map f vmats where
-- >   f : Nat -> Nat
-- >   f i = getWitness (filterP (\ k => mod k i == O) nats (believe_me oh))

> reverseFilter : (alpha -> Bool) -> List alpha -> List alpha
> reverseFilter {alpha} p = foldl f [] where
>   f : List alpha -> alpha -> List alpha
>   f as a = if p a then a :: as else as

> reverseFilter' : (alpha -> Bool) -> List alpha -> List alpha
> reverseFilter' {alpha} p = foldr f [] where
>   f : alpha -> List alpha -> List alpha
>   f a as = if p a then a :: as else as

> reverseFilter'' : (alpha -> Bool) -> List alpha -> List alpha
> reverseFilter'' {alpha} p as = lala p [] as where
>   lala : (alpha -> Bool) -> List alpha -> List alpha -> List alpha
>   lala p e [] = e
>   lala p e (a :: as) = if p a then lala p (a :: e) as else lala p e as
          
> flmats : List Nat
> flmats = map f lmats where
>   f : Nat -> Nat
>   f i = g (reverseFilter'' (\ k => mod k i == O) lnats) where
>     g : List Nat -> Nat
>     g [] = O
>     g (n :: ns) = S O

> main : IO ()
> -- main = putStrLn (show (map cast fvmats))
> main = putStrLn (show (map cast flmats))
