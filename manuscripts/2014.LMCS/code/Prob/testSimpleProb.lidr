> module Main


> import Prob.SimpleProb


> n1 : Nat
> n1 = 1

> n2 : Nat
> n2 = 40

--

> d1 : Float
> d1 = 1.0 / (cast (cast n1))

> xp1 : List (Float, Float)
> xp1 = [(cast (cast i), d1) | i <- [1..n1]]

> sp1 : SimpleProb Float
> sp1 = SP xp1

> ssp1 : List Float
> ssp1 = supp sp1

--

> d2 : Float
> d2 = 1.0 / (cast (cast n2))

> xp2 : List (Float, Float)
> xp2 = [(cast (cast i), d2) | i <- [1..n2]]

> sp2 : SimpleProb Float
> sp2 = SP xp2

> ssp2 : List Float
> ssp2 = supp sp2

--

> sp : SimpleProb Float
> sp = convComb eps sp1 sp2 where
>   eps = 0.1
              
--

> main : IO ()
> main = do 
>   putStrLn ("supp sp1 = "
>             ++
>             (show (map cast ssp1))
>            )
>   putStrLn ("supp sp2 = "
>             ++
>             (show (map cast ssp2))
>            )
>   putStrLn ("supp sp = "
>             ++
>             (show (map cast (supp sp)))
>            )
>   putStrLn ("eValue sp1 = "
>             ++
>             (show (eValue sp1))
>            )
>   putStrLn ("eValue sp2 = "
>             ++
>             (show (eValue sp2))
>            )
>   putStrLn ("eValue sp = "
>             ++
>             (show (eValue sp))
>            )
