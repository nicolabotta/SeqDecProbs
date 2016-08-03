> module Main

> import SimpleProb
> import SimpleProbBasicOperations
> import SimpleProbBasicProperties
> import ListOperations
> import NonNegRationalBasicProperties

> %default total
> %auto_implicits off


> xs : List Nat
> xs = [0,1,2,0]

> sp : SimpleProb Nat
> sp = mkSimpleProb xs ()

> main : IO ()
> main = do putStrLn ("sp           = " ++ show sp)
>           putStrLn ("support sp   = " ++ show (support sp))
>           putStrLn ("probs sp     = " ++ show (probs sp))
>           putStrLn ("normalize sp = " ++ show (normalize sp))
>           putStrLn ("prob sp 0    = " ++ show (prob sp 0))
>           putStrLn ("prob sp 1    = " ++ show (prob sp 1))
>           putStrLn ("prob sp 2    = " ++ show (prob sp 2))
>           putStrLn ("prob sp 3    = " ++ show (prob sp 3))




