> module MaxArgmax


> import DynamicProgramming.S1101_Context

> %default total


OptLemma shows that, given an optimal sequence of policies, an optimal
sequence of controls can be easily computed for any initial value by
means of |ctrl|.

Thus, the problem of computing optimal sequences of controls is reduced
to the problem of computing optimal sequences of policies. This can be
done if we assume that, for all |x : X| and for all |f : Y x -> Float|,
we are able to select a control |y : Y x| which maximises |f|. More
precisely, we assume to have at our disposal

> max : (x : X) -> (Y x -> Float) -> Float

> argmax : (x : X) -> (Y x -> Float) -> Y x

which fulfill the specifications

> MaxSpec  :  Type
> MaxSpec  =  (x : X) ->
>             (f : Y x -> Float) ->
>             (y : Y x) ->
>             so (f y <= max x f)

> ArgmaxSpec  :  Type
> ArgmaxSpec  =  (x : X) ->
>                (f : Y x -> Float) ->
>                so (f (argmax x f) == max x f)

Thas is, we assume to be able to define |maxSpec| and |argmaxSpec| of
type |MaxSpec|, |ArgmaxSpec|, respectively:

> maxSpec : MaxSpec
> argmaxSpec : ArgmaxSpec

