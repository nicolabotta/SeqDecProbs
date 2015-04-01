> module Main where

> sfilter :: (alpha -> Bool) -> [alpha] -> [alpha]
> sfilter p = foldr f []
>   where f a e = if p a then (a : e) else e
          
> rfilter :: (alpha -> Bool) -> [alpha] -> [alpha]
> rfilter p as = foldl f [] as 
>   where f as a = if p a then (a : as) else as          
          
> n :: Int
> n = 4000001

> ints :: [Int]
> ints = [mod i 2 | i <- [1..n]]

> p :: Int -> Bool
> p k = False
          
> fs :: [Int]
> fs = filter p ints

> main = print fs
