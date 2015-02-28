> module RelFloatProperties


> import Data.So
> import Decidable.Order

> import Order
> import RelFloatPostulates
> import SoProperties


> %default total 


> LTE : Float -> Float -> Type
> LTE x y = So (x <= y)


> instance Preorder Float LTE where
>   reflexive = reflexiveFloatLTE
>   transitive x y z xLTEy yLTEz = transitiveFloatLTE xLTEy yLTEz


> instance Preordered Float LTE where
>   preorder = totalFloatLTE


