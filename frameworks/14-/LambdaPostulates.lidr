> module LambdaPostulates


> %default total


> postulate lambdaLemma1 : {A, B : Type} -> (f : A -> B) -> (\ a => f a) = f
