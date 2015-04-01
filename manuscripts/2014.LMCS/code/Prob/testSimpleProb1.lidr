> module Main

-- > mapFilter : (alpha -> beta) ->
-- >             (alpha -> Bool) -> 
-- >             Vect alpha n -> 
-- >             (n : Nat ** Vect beta n)
-- > mapFilter f p Nil = (_ ** Nil)
-- > mapFilter f p (a :: as) with (p a)
-- >   | True  = (_ ** (f a) :: (getProof (mapFilter f p as)))
-- >   | False = mapFilter f p as

> total mapFilter : (alpha -> beta) ->
>                   (alpha -> Bool) -> 
>                   Vect alpha n -> 
>                   (n : Nat ** Vect beta n)
> mapFilter f p Nil = (_ ** Nil)
> mapFilter f p (a :: as) with (mapFilter f p as)
>   | (_ ** tail) = if p a
>                   then (_ ** (f a) :: tail)
>                   else (_ ** tail)

total filter : (a -> Bool) -> Vect a n -> (p ** Vect a p)
filter p [] = ( _ ** [] )
filter p (x::xs) with (filter p xs)
  | (_ ** tail) =
    if p x then
      (_ ** x::tail)
    else
      (_ ** tail)

> data SimpleProb : Type -> Type where
>   SP : (aps : Vect (alpha, Float) n) -> 
>        SimpleProb alpha

> suppBy : (alpha -> alpha -> Bool) -> 
>          SimpleProb alpha -> 
>          (n : Nat ** Vect alpha n) 

-- > suppBy {alpha} p (SP aps) = 
-- >   nubBy p (map fst (getProof (filter notz aps))) where
-- >     notz : (alpha, Float) -> Bool
-- >     notz (_, px) = px /= 0.0

> suppBy {alpha} p (SP aps) = 
>   nubBy p (getProof (mapFilter fst notz aps)) where
>     notz : (alpha, Float) -> Bool
>     notz (_, px) = px /= 0.0

> supp : Eq alpha =>
>        SimpleProb alpha -> 
>        (n : Nat ** Vect alpha n) 
> supp = suppBy (==)

-- test:

> m : Nat -- quadratic
> m = 10

> n : Nat -- quadratic
> n = 20

> N : Nat -- linear
> N = 10

> d : Float
> d = 1.0 / cast (cast (m * n))

> xp : Vect (Nat, Float) (m * n)
> xp = fromList ([(i, d) | i <- [1..m], j <- [1..n]])

> sp : SimpleProb Nat
> sp = SP xp

> is : Vect Nat N
> is = fromList ([1..N])

> ssp : (n : Nat ** Vect Nat n)
> ssp = supp sp

> bs : Vect Bool N
> bs = map (\ n => elem n (getProof (supp sp))) is
> -- bs = map (\ n => elem n (getProof ssp)) is
              
> main : IO ()
> main = putStrLn (show bs)