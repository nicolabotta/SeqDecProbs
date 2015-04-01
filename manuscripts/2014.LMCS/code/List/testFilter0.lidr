> module Main

> n : Nat
> -- n = S 1600
> n = S 100000
      
> nats : List Nat
> nats = [fromInteger i | i <- [1..(cast n)]]

> ints : List Int
> ints = [i | i <- [1..(cast n)]]

> p : Nat -> Bool
> p k = False

> q : Int -> Bool
> q k = False

> -- fs : List Nat
> -- fs = filter p nats
> -- fs = foldl f Nil nats where
> --   f : List Nat -> Nat -> List Nat
> --   f as a = if p a then (a :: as) else as

> fs : List Int
> fs = filter q ints

> main : IO ()
> main = 
>   putStrLn 
>   ((show (head nats (believe_me oh))) 
>    ++
>    (show fs)
>   )
