> getW : {P : a -> Type} -> Sigma a P -> a 
> getW = Prelude.Pairs.Sigma.getWitness

> cong2 : (f : a -> b -> c) -> (a1 = a2) -> (b1 = b2) -> f a1 b1 = f a2 b2
> cong2 f Refl Refl = Refl

> depCross : {P1 : alpha -> Type} ->
>            {P2 : beta -> Type} ->
>            (f : alpha -> beta ** (a : alpha) -> P1 a -> P2 (f a)) -> 
>            (a : alpha ** P1 a) -> 
>            (b : beta ** P2 b)
> depCross (f ** g) (a ** P1a) = (f a ** g a P1a)

> depCrossLemma : {P1 : alpha -> Type} ->
>                 {P2 : alpha -> Type} ->
>                 {f : (a : alpha) -> P1 a -> P2 a} ->
>                 (ac : (a : alpha ** P1 a)) -> 
>                 (getW {P = P2}) (depCross (id ** f) ac) = (getW {P = P1}) ac
> depCrossLemma (a ** c) = Refl
 
> mapGetWMapDepCrossLemma : {P1 : alpha -> Type} ->
>                           {P2 : alpha -> Type} ->
>                           {f : (a : alpha) -> P1 a -> P2 a} ->
>                           (xs : List (a : alpha ** P1 a)) -> 
>                           map (getW {P = P2}) (map (depCross (id ** f)) xs) = map (getW {P = P1}) xs
> mapGetWMapDepCrossLemma Nil = Refl
> mapGetWMapDepCrossLemma {P1} {P2} {f} (x :: xs) = ?lala where
>   gigi : (getW {P = P2}) (depCross (id ** f) x) 
>          = 
>          getW {P = P1} x
>   gigi = depCrossLemma x
>   gaga : map (getW {P = P2}) (map (depCross (id ** f)) xs)
>          =
>          map (getW {P = P1}) xs
>   gaga = mapGetWMapDepCrossLemma xs
>   s1 : map (getW {P = P2}) (map (depCross (id ** f)) (x :: xs)) 
>        = 
>        map (getW {P = P2}) ((depCross (id ** f) x) :: (map (depCross (id ** f)) xs))
>   s1 = Refl
>   s2 : map (getW {P = P2}) ((depCross (id ** f) x) :: (map (depCross (id ** f)) xs))
>        = 
>        ((getW {P = P2}) (depCross (id ** f) x)) :: (map (getW {P = P2}) (map (depCross (id ** f)) xs))
>   s2 = Refl
>   s3 : ((getW {P = P2}) (depCross (id ** f) x)) :: (map (getW {P = P2}) (map (depCross (id ** f)) xs))
>        =
>        ((getW {P = P1}) x) :: (map (getW {P = P1}) xs)
>   s3 = cong2 (::) gigi gaga
>   s4 : ((getW {P = P1}) x) :: (map (getW {P = P1}) xs)
>        =
>        map (getW {P = P1}) (x :: xs)
>   s4 = Refl
>   s5 : map (getW {P = P2}) (map (depCross (id ** f)) (x :: xs)) 
>        =
>        map (getW {P = P1}) (x :: xs)
>   s5 = trans s1 (trans s2 (trans s3 s4))

