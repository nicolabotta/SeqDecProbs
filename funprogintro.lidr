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
