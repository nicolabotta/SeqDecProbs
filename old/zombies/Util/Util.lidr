> module Util


> pair : (a -> b, a -> c) -> a -> (b, c)
> pair (f, g) x = (f x, g x)


> didi : (a -> b, c -> d) -> (a, c) -> (b, d)
> didi (f, g) (a, c) = (f a, g c)
