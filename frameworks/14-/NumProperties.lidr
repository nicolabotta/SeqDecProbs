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
>                  {f : A -> B -> B} -> {e : B} -> 
>                  {a : A} -> {as : Vect n A} ->
>                  foldr f e (a :: as) = f a (foldr f e as)

should hold by definition and should be replaceable by just |Refl|. But
since |Data.VectType.foldr| is implemented in terms of an accumulator
(is there a particular reason for doing so ?) we in fact need a
(possibly non-trivial?) proof.

> |||
> sumLemma : (Num t) => (x : t) -> (xs : Vect m t) -> sum (x :: xs) = x + sum xs
> sumLemma x xs = ( sum (x :: xs) )
>               ={ Refl }=
>                 ( foldr (+) (fromInteger 0) (x :: xs) )
>               ={ foldrVectLemma }=
>                 ( x + foldr (+) (fromInteger 0) xs )
>               ={ Refl }=
>                 ( x + sum xs )
>               QED

> |||
> -- multSumLemma : (NumMultZeroPlus t, NumMultDistributesOverPlus t) =>
> multSumLemma : (NumMultZeroPlus t) =>
>                (x : t) -> (xs : Vect m t) ->
>                x * sum xs = sum (multSV x xs)
> multSumLemma x  Nil      = ( x * (fromInteger 0) )
>                          ={ multZeroPlusRight x }=
>                            ( fromInteger 0 )
>                          ={ Refl }=
>                            ( sum Data.VectType.Vect.Nil )
>                          QED
> multSumLemma x (y :: ys) = ( x * (sum (y :: ys)) )
>                          ={ replace {x = sum (y :: ys)}
>                                     {y = y + sum ys}
>                                     {P = \ ZUZU => x * (sum (y :: ys)) = x * ZUZU}
>                                     (sumLemma y ys)
>                                     Refl }=
>                            ( x * (y + sum ys) )
>                          ={ ?loki }=
>                          -- ={ multDistributesOverPlusRight x y (sum ys) }=
>                            ( x * y + x * sum ys )
>                          ={ replace {x = x * sum ys}
>                                     {y = sum (multSV x ys)}
>                                     {P = \ ZUZU => x * y + x * sum ys = x * y + ZUZU}
>                                     (multSumLemma x ys)
>                                     Refl }=
>                            ( x * y + sum (multSV x ys) )
>                          ={ sym (sumLemma (x * y) (multSV x ys)) }=     
>                            ( sum (x * y :: (multSV x ys)) )
>                          ={ Refl }=
>                            ( sum (multSV x (y :: ys)) )
>                          QED

> |||
> multVMLemma : (Num t) => 
>               (xs : Vect m t) -> (xss : Matrix m n t) ->
>               sum xs = (fromInteger 1) ->
>               (k : Fin m -> sum (row k xss) = fromInteger 1) -> 
>               sum (toVect (multVM xs xss)) = fromInteger 1 
   
