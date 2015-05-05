> module Util

> pair : (a -> b, a -> c) -> a -> (b, c)
> pair (f, g) x = (f x, g x)
