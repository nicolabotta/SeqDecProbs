> module NumRefinements


> %default total

> class (Num t) => NumPlusZeroPlus t where
>   plusZeroPlusRight : (x : t) -> x + (fromInteger 0) = x
>   plusZeroPlusLeft  : (x : t) -> (fromInteger 0) + x = x
>
> class (NumPlusZeroPlus t) => NumAssocPlus t where
>   plusAssoc : (x : t) -> (y : t) -> (z : t) -> x + (y + z) = (x + y) + z


This should not depend on the anything more than Num, bu Idris
currently (2015-08-08) seems to have problems when combining two
classes constraining the same type so this is a temporary work-around.

class (Num t) => NumMultZeroPlus t where

> class (NumAssocPlus t) => NumMultZeroPlus t where
>   multZeroPlusRight : (x : t) -> x * (fromInteger 0) = fromInteger 0
>   multZeroPlusLeft  : (x : t) -> (fromInteger 0) * x = fromInteger 0
>   multOneRight      : (x : t) -> x * (fromInteger 1) = x
>   multOneLeft       : (x : t) -> (fromInteger 1) * x = x
>
> class (NumMultZeroPlus t) => NumMultDistributesOverPlus t where
>   multDistributesOverPlusRight : (x : t) -> (y : t) -> (z : t) ->
>                                  x * (y + z) = (x * y) + (x * z)
>   multDistributesOverPlusLeft  : (x : t) -> (y : t) -> (z : t) ->
>                                  (x + y) * z = (x * z) + (y * z)
