> module Num

> import Data.Fin
> import Data.Vect
> import Data.VectType
> import Syntax.PreorderReasoning

> import Matrix
> import MatrixOperations
> import NumRefinements
> import NumOperations

> %default total


The following

> foldrVectLemma : {A, B : Type} -> {n : Nat} ->
>                  (f : A -> B -> B) -> (e : B) ->
>                  (a : A) -> (as : Vect n A) ->
>                  foldr f e (a :: as) = f a (foldr f e as)

should hold by definition and should be replaceable by just |Refl|. But
since |Data.VectType.foldr| is implemented in terms of an accumulator
(is there a particular reason for doing so ?) we in fact need a
(possibly non-trivial?) proof.


> total foldrClassic : (t -> acc -> acc) -> acc -> Vect n t -> acc
> foldrClassic f e [] = e
> foldrClassic f e (x::xs) = f x (foldrClassic f e xs)

> foldrImplLemma : {A, B : Type} -> {n : Nat} ->
>                  (f : A -> B -> B) -> (e : B) -> (go : B -> B) ->
>                  (as : Vect n A) ->
>                  foldrImpl f e go as = go (foldrClassic f e as)
> foldrImplLemma f e go [] = Refl
> foldrImplLemma f e go (a :: as) =
>     ( foldrImpl f e go (a :: as) )
>   ={ Refl }=
>     ( foldrImpl f e (go . (f a)) as )
>   ={ foldrImplLemma f e (go . (f a)) as }=
>     ( (go . (f a)) (foldrClassic f e as) )
>   ={ Refl }=
>     ( go (f a (foldrClassic f e as)) )
>   ={ Refl }=
>     ( go (foldrClassic f e (a :: as) ) )
>   QED

> foldrImplCorr :  {A, B : Type} -> {n : Nat} ->
>                  (f : A -> B -> B) -> (e : B) ->
>                  (as : Vect n A) ->
>                  foldrImpl f e id as = foldrClassic f e as
> foldrImplCorr f e as = foldrImplLemma f e id as

Now we can continue with the proof:

> foldrVectLemma f e a as =
>     ( foldr f e (a :: as) )
>   ={ Refl }=
>     ( foldrImpl f e id (a :: as) )
>   ={ foldrImplCorr f e (a :: as) }=
>     ( foldrClassic f e (a :: as) )
>   ={ Refl }=
>     ( f a (foldrClassic f e as) )
>   ={ cong {f = f a} (sym (foldrImplCorr f e as)) }=
>     ( f a (foldrImpl f e id as) )
>   ={ Refl }=
>     ( f a (foldr f e as) )
>   QED

> |||
> sumLemma : (Num t) => (x : t) -> (xs : Vect m t) -> sum (x :: xs) = x + sum xs
> sumLemma x xs = ( sum (x :: xs) )
>               ={ Refl }=
>                 ( foldr (+) (fromInteger 0) (x :: xs) )
>               ={ foldrVectLemma (+) (fromInteger 0) x xs }=
>                 ( x + foldr (+) (fromInteger 0) xs )
>               ={ Refl }=
>                 ( x + sum xs )
>               QED

> |||
> multSumLemma : (NumMultDistributesOverPlus t) =>
>                (x : t) -> (xs : Vect m t) ->
>                x * sum xs = sum (multSV x xs)
> multSumLemma x  Nil      = ( x * (fromInteger 0) )
>                          ={ multZeroPlusRight x }=
>                            ( fromInteger 0 )
>                          ={ Refl }=
>                            ( sum Data.VectType.Vect.Nil )
>                          QED
> multSumLemma x (y :: ys) = ( x * (sum (y :: ys)) )
>                          ={ cong (sumLemma y ys) }=
>                            ( x * (y + sum ys) )
>                          ={ NumRefinements.multDistributesOverPlusRight x y (sum ys) }=
>                            ( (x * y) + (x * sum ys) )
>                          ={ cong (multSumLemma x ys) }=
>                            ( x * y + sum (multSV x ys) )
>                          ={ sym (sumLemma (x * y) (multSV x ys)) }=
>                            ( sum (x * y :: multSV x ys) )
>                          ={ Refl }=
>                            ( sum (multSV x (y :: ys)) )
>                          QED

> |||
> multVMLemma : (Num t) =>
>               (xs : Vect m t) -> (xss : Matrix m n t) ->
>               sum xs = (fromInteger 1) ->
>               (k : Fin m -> sum (row k xss) = fromInteger 1) ->
>               sum (toVect (multVM xs xss)) = fromInteger 1
