> getW : (P : a -> Type) -> Sigma a P -> a 
> getW P = Prelude.Pairs.Sigma.getWitness

> cong2 : (f : a -> b -> c) -> (a1 = a2) -> (b1 = b2) -> f a1 b1 = f a2 b2
> cong2 f Refl Refl = Refl

> depCross : (P1 : alpha -> Type) ->
>            (P2 : beta -> Type) ->
>            (f : alpha -> beta ** (a : alpha) -> P1 a -> P2 (f a)) -> 
>            (a : alpha ** P1 a) -> 
>            (b : beta ** P2 b)
> depCross P1 P2 (f ** g) (a ** P1a) = (f a ** g a P1a)

> depCrossLemma : (P1 : alpha -> Type) ->
>                 (P2 : alpha -> Type) ->
>                 (f : (a : alpha) -> P1 a -> P2 a) ->
>                 (ac : (a : alpha ** P1 a)) -> 
>                 getW P2 (depCross P1 P2 (id ** f) ac) = getW P1 ac
> depCrossLemma P1 P2 f (a ** c) = Refl

> mapGetWMapDepCrossLemma : (P1 : alpha -> Type) ->
>                           (P2 : alpha -> Type) ->
>                           (f : (a : alpha) -> P1 a -> P2 a) ->
>                           (xs : List (a : alpha ** P1 a)) -> 
>                           map (getW P2) (map (depCross P1 P2 (id ** f)) xs) 
>                           = 
>                           map (getW P1) xs
> mapGetWMapDepCrossLemma P1 P2 f Nil = Refl
> mapGetWMapDepCrossLemma P1 P2 f (x :: xs) = s5 where
>   s1 : map (getW P2) (map (depCross P1 P2 (id ** f)) (x :: xs)) 
>        = 
>        map (getW P2) ((depCross P1 P2 (id ** f) x) :: (map (depCross P1 P2 (id ** f)) xs))
>   s1 = Refl
>   s2 : map (getW P2) ((depCross P1 P2 (id ** f) x) :: (map (depCross P1 P2 (id ** f)) xs))
>        = 
>        (getW P2 (depCross P1 P2 (id ** f) x)) :: (map (getW P2) (map (depCross P1 P2 (id ** f)) xs))
>   s2 = Refl
>   s3 : (getW P2 (depCross P1 P2 (id ** f) x)) :: (map (getW P2) (map (depCross P1 P2 (id ** f)) xs))
>        =
>        (getW P1 x) :: (map (getW P1) xs)
>   s3 = cong2 (::) (depCrossLemma P1 P2 f x) (mapGetWMapDepCrossLemma P1 P2 f xs)
>   s4 : (getW P1 x) :: (map (getW P1) xs)
>        =
>        map (getW P1) (x :: xs)
>   s4 = Refl
>   s5 : map (getW P2) (map (depCross P1 P2 (id ** f)) (x :: xs)) 
>        =
>        map (getW P1) (x :: xs)
>   s5 = trans s1 (trans s2 (trans s3 s4))

