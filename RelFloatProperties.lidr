> module RelFloatProperties


> import Data.So
> import Decidable.Order

> import Preorder
> import TotalPreorder
> import RelFloat
> import RelFloatPostulates
> import SoProperties


> %default total 


> preorderFloatLTE : Preorder Float
> preorderFloatLTE = 
>   MkPreorder FloatLTE reflexiveFloatLTE transitiveFloatLTE


> totalPreorderFloatLTE : TotalPreorder Float
> totalPreorderFloatLTE = 
>   MkTotalPreorder FloatLTE reflexiveFloatLTE transitiveFloatLTE totalFloatLTE




