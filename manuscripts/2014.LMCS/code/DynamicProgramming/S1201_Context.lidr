> module Context


> %default total


> State   :  (t : Nat) -> Type
> Ctrl    :  (t : Nat) -> State t -> Type
> step    :  (t : Nat) -> (x : State t) -> Ctrl t x -> State (S t)
> reward  :  (t : Nat) -> (x : State t) -> Ctrl t x -> State (S t) -> Float
