> module NumProperties

> import Data.Fin
> import Data.Vect
> import Syntax.PreorderReasoning

> %default total
> %access public export

> interface (Num t) => NumMultZeroOne t where
>   multZeroRightZero   : (x : t) -> x * 0 = 0
>   multZeroLeftZero    : (x : t) -> 0 * x = 0
>   multOneRightNeutral : (x : t) -> x * 1 = x
>   multOneLeftNeutral  : (x : t) -> 1 * x = x

> -- interface (Num t) => NumMultDistributesOverPlus t where
> interface (NumMultZeroOne t) => NumMultDistributesOverPlus t where
>   multDistributesOverPlusRight : (x, y, z : t) -> x * (y + z) = (x * y) + (x * z)
>   multDistributesOverPlusLeft  : (x, y, z : t) -> (x + y) * z = (x * z) + (y * z)

> multSV : (Num t) => t -> Vect m t -> Vect m t
> multSV x = map (x *)

> postulate sumLemma : (Num t) => (x : t) -> (xs : Vect m t) -> sum (x :: xs) = x + sum xs

> -- multSumLemma : (NumMultZeroOne t, NumMultDistributesOverPlus t) =>
> multSumLemma : (NumMultDistributesOverPlus t) =>
>                (x : t) -> (xs : Vect m t) ->
>                x * sum xs = sum (multSV x xs)
> multSumLemma x  Nil      = ( x * (fromInteger 0) )
>                          ={ multZeroRightZero x }=
>                            ( fromInteger 0 )
>                          ={ Refl }=
>                            ( sum Data.Vect.Nil )
>                          QED
> multSumLemma x (y :: ys) = ( x * (sum (y :: ys)) )
>                          ={ cong (sumLemma y ys) }=
>                            ( x * (y + sum ys) )
>                          ={ multDistributesOverPlusRight x y (sum ys) }=
>                            ( (x * y) + (x * sum ys) )
>                          ={ cong (multSumLemma x ys) }=
>                            ( x * y + sum (multSV x ys) )
>                          ={ sym (sumLemma (x * y) (multSV x ys)) }=
>                            ( sum (x * y :: multSV x ys) )
>                          ={ Refl }=
>                            ( sum (multSV x (y :: ys)) )
>                          QED

