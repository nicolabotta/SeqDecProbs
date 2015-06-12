> module DecEq


> %default total


> class DecEq alpha where
>   dec_eq : (a : alpha) -> 
>            (a' : alpha) ->
>            Either (a = a') (Not (a = a'))

