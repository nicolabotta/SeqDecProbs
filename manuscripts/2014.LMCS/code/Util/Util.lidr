> module Util

> %default total
> %access public export


> pair : (a -> b, a -> c) -> a -> (b, c)
> pair (f, g) x = (f x, g x)

