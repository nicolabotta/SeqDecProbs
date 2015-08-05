> module Num

> import Data.Fin
> import Data.Vect
> import Data.VectType
> import Syntax.PreorderReasoning

> %default total


> ||| Scalar vector multiplication
> multSV : (Num t) => t -> Vect m t -> Vect m t
> multSV _ Nil = Nil
> multSV x (y :: ys) = (x * y) :: (multSV x ys)

> ||| 
> multConcat : (Num t) => Vect m t -> Vect m (Vect n t) -> Vect (m * n) t
> multConcat {m = Z}   {n} Nil Nil = Nil
> multConcat {m = S l} {n} (x :: xs) (v :: vs) = (multSV x v) ++ multConcat xs vs


To be put in a NumPredicates.lidr file

> class (Num t) => NumPlusMonoid t where
>   rightNeutralPlusZero : (x : t) -> x + (fromInteger 0) = x 

> class (Num t) => NumMultPlusZero t where
>   multPlusZeroRight : (x : t) -> x * (fromInteger 0) = fromInteger 0

> class (Num t) => NumMultDistributesOverPlus t where
>   multDistributesOverPlusRight : (x : t) -> (y : t) -> (z : t) ->
>                                  x * (y + z) = (x * y) + (x * z)


To be put in a NumProperties.lidr file:


> foldrVectLemma : {A, B : Type} -> {n : Nat} -> {f : A -> B -> B} -> {e : B} -> {a : A} -> {as : Vect n A} ->
>                  foldr f e (a :: as) = f a (foldr f e as)

> sumLemma : (Num t) => (x : t) -> (xs : Vect m t) -> sum (x :: xs) = x + sum xs
> sumLemma x xs = ( sum (x :: xs) )
>               ={ Refl }=
>                 ( foldr (+) (fromInteger 0) (x :: xs) )
>               ={ foldrVectLemma }=
>                 ( x + foldr (+) (fromInteger 0) xs )
>               ={ Refl }=
>                 ( x + sum xs )
>               QED

> -- multSumLemma : (NumMultPlusZero t, NumMultDistributesOverPlus t) =>
> multSumLemma : (NumMultPlusZero t) =>
>                (x : t) -> (xs : Vect m t) ->
>                x * sum xs = sum (multSV x xs)
> multSumLemma x  Nil      = ( x * (fromInteger 0) )
>                          ={ multPlusZeroRight x }=
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
>                          ={ ?luki }=
>                            ( x * y + sum (multSV x ys) )
>                          ={ sym (sumLemma (x * y) (multSV x ys)) }=     
>                            ( sum (x * y :: (multSV x ys)) )
>                          ={ Refl }=
>                            ( sum (multSV x (y :: ys)) )
>                          QED

> multConcatLemma : (Num t) => 
>                   (xs : Vect m t) -> (vs : Vect m (Vect n t)) ->
>                   sum xs = (fromInteger 1) ->
>                   (k : Fin m -> sum (Data.VectType.Vect.index k vs) = fromInteger 1) -> 
>                   sum (multConcat xs vs) = fromInteger 1 
   
