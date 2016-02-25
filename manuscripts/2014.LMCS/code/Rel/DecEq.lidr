> module DecEq

> -- import Logic.Ops


> interface DecEq alpha where
>   dec_eq : (a : alpha) ->
>            (a' : alpha) ->
>            Either (a = a') (Not (a = a'))
