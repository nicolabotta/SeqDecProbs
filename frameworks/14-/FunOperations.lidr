> module FunOperations

> import Data.So


> %default total

> %access public export


> ||| 
> pair : (a -> b, a -> c) -> a -> (b, c)
> pair (f, g) x = (f x, g x)


> ||| 
> cross : (a -> c) -> (b -> d) -> (a, b) -> (c, d)
> cross f g (x, y) = (f x, g y)


> |||
> modifyFun : {a : Type} -> {b : Type} -> (Eq a) => 
>             (a -> b) -> a -> b -> (a -> b)
> modifyFun f a b a' = if a' == a then b else f a'

> {-

> soTrue :  So b -> b = True

> reflexive_eqeq : (Eq a) => (x : a) -> So (x == x)

> modifyFunLemma : {a : Type} -> {b : Type} -> (Eq a) => 
>                  (f : a -> b) -> (x : a) -> (y : b) ->
>                  modifyFun f x y x = y
> modifyFunLemma f x y = replace {P = \ z => ifThenElse (x == x) y (f x) = ifThenElse z y (f x)} 
>                                (soTrue (reflexive_eqeq x)) 
>                                Refl

> -}

