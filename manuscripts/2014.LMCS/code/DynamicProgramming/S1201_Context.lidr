> module Context


> %default total


In the case of a time-dependent set of states and of a deterministic
transition function, the context of a DP problem can be formalized in
terms of:

# A set of states |X|:

> X : (t : Nat) -> Type

# A set of controls or actions |Y t x|:

> Y : (t : Nat) -> X t -> Type

# A deterministic transition function:

> step : (t : Nat) -> (x : X t) -> Y t x -> X (S t)

# A reward function:

> reward : (t : Nat) -> (x : X t) -> Y t x -> X (S t) -> Float

