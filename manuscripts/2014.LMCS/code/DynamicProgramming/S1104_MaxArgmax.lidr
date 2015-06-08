> module MaxArgmax

> import Data.So

> import DynamicProgramming.S1101_Context

> %default total


> max     :  (x : State) -> (Ctrl x -> Float) -> Float
> argmax  :  (x : State) -> (Ctrl x -> Float) -> Ctrl x

> MaxSpec     :  Type
> MaxSpec     =  (x : State) -> (f : Ctrl x -> Float) -> (y : Ctrl x) ->
>                So (f y <= max x f)
> ArgmaxSpec  :  Type
> ArgmaxSpec  =  (x : State) -> (f : Ctrl x -> Float) ->
>                So (f (argmax x f) == max x f)

Thas is, we assume to be able to define |maxSpec| and |argmaxSpec| of
type |MaxSpec|, |ArgmaxSpec|, respectively:

> maxSpec : MaxSpec
> argmaxSpec : ArgmaxSpec

