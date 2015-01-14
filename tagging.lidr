> module Tagging

> import Data.List
 

> %default total 

> getW : {P : a -> Type} -> Sigma a P -> a 
> getW = Prelude.Pairs.Sigma.getWitness

> mapSnd : {alpha : Type} -> {P1 : alpha -> Type} -> {P2 : alpha -> Type} -> 
>          (f : (a : alpha) -> P1 a -> P2 a) -> (a : alpha ** P1 a) -> (a : alpha ** P2 a)
> mapSnd f (a ** b) = (a ** f a b)

> mapSndLemma : {alpha : Type} -> {P1 : alpha -> Type} -> {P2 : alpha -> Type} -> 
>               (f : (a : alpha) -> P1 a -> P2 a) ->
>               (ab : (a : alpha ** P1 a)) -> 
>               getW (mapSnd f ab) = getW ab
> mapSndLemma f (a ** Pa) = Refl

> f : (a' : alpha) -> (a : alpha ** a `Elem` as) -> (a : alpha ** a `Elem` (a' :: as))
> -- f a' (a ** prf) = (a ** There prf)
> f a' = mapSnd (\ a => \ b => There b) 

> tagElemList : (as : List alpha) -> List (a : alpha ** a `Elem` as)
> tagElemList Nil = Nil
> tagElemList (a :: as) = (a ** Here) :: (map (f a) (tagElemList as))

> cong2 : (f : a -> b -> c) -> (a1 = a2) -> (b1 = b2) -> f a1 b1 = f a2 b2
> cong2 f Refl Refl = Refl

> tagElemListSpec : (as : List alpha) -> map getW (tagElemList as) = as
> tagElemListSpec Nil = Refl
> tagElemListSpec (a :: as) = s5 where
>   s1 : a = a
>   s1 = Refl 
>   s2 : map getW (tagElemList as) = as
>   s2 = tagElemListSpec as
>   s3 : map getW (tagElemList (a :: as)) = map getW ((a ** Here) :: (map (f a) (tagElemList as)))
>   s3 = Refl
>   s4 : map getW ((a ** Here) :: (map (f a) (tagElemList as))) = a :: map getW (map (f a) (tagElemList as))
>   s4 = Refl
>   s5 : a :: map getW (map (f a) (tagElemList as)) = a :: map getW (map (f a) (tagElemList as))
>   s5 = cong2 (::) Refl ()
>   s6 : map getW (tagElemList (a :: as)) = a :: as
>   s6 = ?lala -- cong2 (::) s1 s2

