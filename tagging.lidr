> module Tagging

> import Data.List


> %default total


> getW : {A : Type} -> {P : A -> Type} -> Sigma A P -> A
> getW = Prelude.Pairs.Sigma.getWitness


> cong2 : {A, B, C : Type} -> {a1, a2 : A} -> {b1, b2 : B} ->
>         (f : A -> B -> C) -> (a1 = a2) -> (b1 = b2) -> f a1 b1 = f a2 b2
> cong2 f Refl Refl = Refl


> cross : {A, B, C, D : Type} -> (A -> C, B -> D) -> (A, B) -> (C, D)
> cross (f, g) (a, b) = (f a, g b)


> crossLemma : {A, B, D : Type} -> {f : B -> D} ->
>              (ab : (A, B)) -> fst (cross (id, f) ab) = fst ab
> crossLemma (a, b) = Refl


> mapFstMapCrossLemma : (acs : List (a, c)) -> map fst (map (cross (id, f)) acs) = map fst acs
> mapFstMapCrossLemma Nil = Refl
> mapFstMapCrossLemma {f} (ac :: acs) = s5 where
>   s1 : map fst (map (cross (id, f)) (ac :: acs))
>        =
>        map fst (((cross (id, f)) ac) :: (map (cross (id, f)) acs))
>   s1 = Refl
>   s2 : map fst (((cross (id, f)) ac) :: (map (cross (id, f)) acs))
>        =
>        fst ((cross (id, f)) ac) :: (map fst (map (cross (id, f)) acs))
>   s2 = Refl
>   s3 : fst ((cross (id, f)) ac) :: (map fst (map (cross (id, f)) acs))
>        =
>        fst ac :: (map fst acs)
>   s3 = cong2 (::) (crossLemma ac) (mapFstMapCrossLemma acs)
>   s4 : fst ac :: (map fst acs)
>        =
>        map fst (ac :: acs)
>   s4 = Refl
>   s5 : map fst (map (cross (id, f)) (ac :: acs)) = map fst (ac :: acs)
>   s5 = trans s1 (trans s2 (trans s3 s4))


> depCross : {A, B : Type} -> {P1 : A -> Type} -> {P2 : B -> Type} ->
>            (f : A -> B ** (a : A) -> P1 a -> P2 (f a)) -> (a : A ** P1 a) -> (b : B ** P2 b)
> depCross (f ** g) (a ** P1a) = (f a ** g a P1a)


> depCrossLemma : {A : Type} -> {P1 : A -> Type} -> {P2 : A -> Type} ->
>                 {f : (a : A) -> P1 a -> P2 a} ->
>                 (p : (a : A ** P1 a)) -> getW (depCross (id ** f) p) = getW p
> depCrossLemma (a ** p1a) = Refl


> mapGetWMapDepCrossLemma : {A : Type} -> {P1 : A -> Type} -> {P2 : A -> Type} ->
>                           {f : (a : A) -> P1 a -> P2 a} ->
>                           (xs : List (a : A ** P1 a)) ->
>                           map (getW {P = P2}) (map (depCross (id ** f)) xs) = map (getW {P = P1}) xs
> mapGetWMapDepCrossLemma Nil = Refl
> mapGetWMapDepCrossLemma {A} {P1} {P2} {f} (x :: xs) = s5 where
>   gigi : getW (depCross (id ** f) x)
>          =
>          getW x
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
>   s3 = ?kika -- cong2 (::) gigi gaga
>   s4 : ((getW {P = P1}) x) :: (map (getW {P = P1}) xs)
>        =
>        map (getW {P = P1}) (x :: xs)
>   s4 = Refl
>   s5 : map (getW {P = P2}) (map (depCross (id ** f)) (x :: xs))
>        =
>        map (getW {P = P1}) (x :: xs)
>   s5 = trans s1 (trans s2 (trans s3 s4))


> f : (a : alpha) -> (a' : alpha) -> (a' `Elem` as) -> (a' `Elem` (a :: as))
> f a a' prf = There prf


> {-

> tagElemList : (as : List alpha) -> List (a : alpha ** a `Elem` as)
> tagElemList Nil = Nil
> tagElemList (a :: as) = (a ** Here) :: (map (depCross (id ** f a)) (tagElemList as))

> tagElemListSpec : (as : List alpha) -> map getW (tagElemList as) = as
> tagElemListSpec Nil = Refl
> tagElemListSpec {alpha} (a :: as) = s5 where
>   P : alpha -> Type
>   P = \ a' => a' `Elem` (a :: as)
>   P' : alpha -> Type
>   P' = \ a' => a' `Elem` as
>   lhs : List (a' : alpha ** a' `Elem` (a :: as))
>   lhs = tagElemList (a :: as)
>   rhs : List (a' : alpha ** a' `Elem` (a :: as))
>   rhs = (a ** Here) :: (map (depCross (id ** f a)) (tagElemList as))
>   rhs' : List (a' : alpha ** a' `Elem` (a :: as))
>   rhs' = map (depCross (id ** f a)) (tagElemList as)
>   s0 : lhs = rhs
>   s0 = Refl
>   s1 : map getW lhs = map getW rhs
>   s1 = Refl
>   s2 : map getW rhs = (getW {P}) (a ** Here) :: (map (getW {P}) rhs')
>   s2 = Refl
>   s3 : (getW {P}) (a ** Here) :: (map (getW {P}) rhs')
>        =
>        a :: (map (getW {P = P'}) (tagElemList as))
>   s3 = cong2 (::) Refl (mapGetWMapDepCrossLemma {P2 = \ a' => Elem a' (a :: as)} {f = f a} (tagElemList as))
>   s4 : a :: (map getW (tagElemList as))
>        =
>        a :: as
>   s4 = cong2 (::) Refl (tagElemListSpec as)
>   s5 : map getW (tagElemList (a :: as))
>        =
>        a :: as
>   s5 = trans s1 (trans s2 (trans s3 s4))

> {-

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
> f a' = mapSnd (\ a, b => There b)

> tagElemList : (as : List alpha) -> List (a : alpha ** a `Elem` as)
> tagElemList Nil = Nil
> tagElemList (a :: as) = (a ** Here) :: (map (f a) (tagElemList as))

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
>   s5 = ?gugu -- cong2 (::) Refl ()
>   s6 : map getW (tagElemList (a :: as)) = a :: as
>   s6 = ?lala -- cong2 (::) s1 s2
> -}

> --}
