> module Main

> import Prob.SimpleProb

> castN2D : Nat -> Double
> castN2D = cast {to = Double} {from = Int} . cast

> n1 : Nat
> n1 = 1

> n2 : Nat
> n2 = 40

--

> d1 : Double
> d1 = 1.0 / (castN2D n1)

> xp1 : List (Double, Double)
> xp1 = [(castN2D i, d1) | i <- [1..n1]]

> sp1 : SimpleProb Double
> sp1 = SP xp1

> ssp1 : List Double
> ssp1 = supp sp1

--

> d2 : Double
> d2 = 1.0 / (castN2D n2)

> xp2 : List (Double, Double)
> xp2 = [(castN2D i, d2) | i <- [1..n2]]

> sp2 : SimpleProb Double
> sp2 = SP xp2

> ssp2 : List Double
> ssp2 = supp sp2

--

> sp : SimpleProb Double
> sp = convComb eps sp1 sp2 where
>   eps = 0.1

--

> main : IO ()
> main = do
>   putStrLn ("supp sp1 = "      ++            (show ssp1)           )
>   putStrLn ("supp sp2 = "      ++            (show ssp2)           )
>   putStrLn ("supp sp = "       ++            (show (supp sp))      )
>   putStrLn ("eValue sp1 = "    ++            (show (eValue sp1))   )
>   putStrLn ("eValue sp2 = "    ++            (show (eValue sp2))   )
>   putStrLn ("eValue sp = "     ++            (show (eValue sp))    )
