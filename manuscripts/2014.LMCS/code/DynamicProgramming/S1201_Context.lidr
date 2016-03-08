> module Context


> %default total

> %access public export


> State   :  (t : Nat) -> Type
> Ctrl    :  (t : Nat) -> State t -> Type
> step    :  (t : Nat) -> (x : State t) -> Ctrl t x -> State (S t)
> reward  :  (t : Nat) -> (x : State t) -> Ctrl t x -> State (S t) -> Double
