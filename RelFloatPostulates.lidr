> module RelFloatPostulates


> import Data.So

> import SoProperties


> %default total 


LTE properties

> ||| 
> postulate reflexiveFloatLTE : 
>   (x : Float) -> So (x <= x)


> |||
> postulate transitiveFloatLTE : 
>   {x : Float} -> {y : Float} -> {z : Float} ->
>   So (x <= y) -> So (y <= z) -> So (x <= z)


> |||
> totalFloatLTE : 
>   (x : Float) -> (y : Float) -> 
>   Either (So (x <= y)) (So (y <= x))


> |||
> postulate monotoneFloatPlusLTE : 
>   {x : Float} -> {y : Float} -> 
>   (z : Float) -> So (x <= y) -> So (z + x <= z + y)


