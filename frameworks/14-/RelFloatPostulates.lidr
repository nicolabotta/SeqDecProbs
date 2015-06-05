> module RelFloatPostulates


> import Data.So

> import SoProperties
> import RelFloat


> %default total


FloatLTE properties

> |||
> postulate reflexiveFloatLTE :
>   (x : Float) -> FloatLTE x x


> |||
> postulate transitiveFloatLTE :
>   (x : Float) -> (y : Float) -> (z : Float) ->
>   FloatLTE x y -> FloatLTE y z -> FloatLTE x z


> |||
> postulate totalFloatLTE :
>   (x : Float) -> (y : Float) ->
>   Either (FloatLTE x y) (FloatLTE y x)


> |||
> postulate monotoneFloatPlusLTE :
>   {x : Float} -> {y : Float} ->
>   (z : Float) -> x `FloatLTE` y -> (z + x) `FloatLTE` (z + y)
