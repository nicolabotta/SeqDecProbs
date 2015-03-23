> module RelFloatProperties


> import Data.So
> import Decidable.Order

> import Order
> import RelFloat
> import RelFloatPostulates
> import SoProperties


> %default total 


> instance Preorder Float FloatLTE where
>   reflexive = reflexiveFloatLTE
>   transitive x y z xLTEy yLTEz = transitiveFloatLTE xLTEy yLTEz


> instance Preordered Float FloatLTE where
>   preorder = totalFloatLTE


