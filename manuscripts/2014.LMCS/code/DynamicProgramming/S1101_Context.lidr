> module Context

> %default total


> State   :  Type
> Ctrl    :  (x : State) -> Type
> step    :  (x : State) -> (y : Ctrl x) -> State
> reward  :  (x : State) -> (y : Ctrl x) -> (x' : State) -> Float
