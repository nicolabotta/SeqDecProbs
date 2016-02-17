> module LambdaPostulates


> %default total


> lambdaLemma1 : {A, B : Type} -> (f : A -> B) -> (\ a => f a) = f
> lambdaLemma1 f = Refl
