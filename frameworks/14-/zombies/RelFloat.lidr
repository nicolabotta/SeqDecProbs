> module RelFloat


> import Data.So

 
> %default total 


> |||
> data FloatLTE : Float -> Float -> Type where
>   LTE : {x : Float} -> {y : Float} -> So (x <= y) -> FloatLTE x y


> |||
> data FloatLT : Float -> Float -> Type where
>   LT : {x : Float} -> {y : Float} -> So (x < y) -> FloatLT x y
