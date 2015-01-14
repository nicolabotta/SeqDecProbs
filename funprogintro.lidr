> postulate  A : Type
> postulate  B : Type
> postulate  C : Type
> postulate  f : A -> B
> postulate  g : A -> B -> c
> postulate  x : A
> postulate  y : B

> test1 : B
> test1 = f x
> test2 : C
> test2 = (g x) y
> test3 : Int
> test3 = 2 + 3
> gx : B -> C
> gx = g x

> aNumber : Nat
> aNumber = 1738

> aFun : Nat -> Nat
> aFun = \x => 2*x+1

> aFun' : Nat -> Nat
> aFun' x = 2*x+1

> infixr 10 ^
> (^) : Float -> Nat -> Float
> x ^ Z      = 1
> x ^ (S n)  = x * (x^n)


> curry : ((a, b) -> c) -> a -> b -> c
> curry f a b = f (a, b)
> 
> uncurry : (a -> b -> c) -> (a, b) -> c
> uncurry f (a, b) = f a b

> discount : Float -> (Nat -> A -> Float) -> (Nat -> A -> Float)
> discount   rate     reward              =  \t =>  \x => rate^t * reward t x

