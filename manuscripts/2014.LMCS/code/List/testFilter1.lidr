> module Main

> sfilter : (alpha -> Bool) -> List alpha -> List alpha
> sfilter {alpha} p = foldr f Nil where
>   f : alpha -> List alpha -> List alpha
>   f a e = if p a then a :: e else e

> rfilter : (alpha -> Bool) -> List alpha -> List alpha
> rfilter {alpha} p = foldl f Nil where
>   f : List alpha -> alpha -> List alpha
>   f e a = if p a then a :: e else e

> n : Nat
> n = S 800
      
> nats : List Nat
> nats = concat ([[0,1] | i <- [1..n]])

> ints : List Int
> ints = concat ([[0,1] | i <- [1..(cast n)]])

> cats : List Char
> cats = concat ([['a','b'] | i <- [1..(cast n)]])

> p : alpha -> Bool
> p _ = False

> fs : List Nat
> fs = filter p nats

> -- fs : List Int
> -- fs = filter p ints

> -- fs : List Char
> -- fs = filter p cats

> main : IO ()
> main = 
>   putStrLn 
>   ((show (head nats (believe_me oh)))
>    ++
>    (show (head ints (believe_me oh))) 
>    ++
>    (show (head cats (believe_me oh))) 
>    ++
>    (show fs)
>   )
