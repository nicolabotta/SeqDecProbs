> module NonDeterministic

> %default total 


> X : (t : Nat) -> Type

> Y : (t : Nat) -> (x : X t) -> Type

> step : (t : Nat) -> (x : X t) -> (y : Y t x) -> List (X (S t))

> reward : (t : Nat) -> (x : X t) -> (y : Y t x) -> (x' : X (S t)) -> Double

> fmap : {A, B : Type} -> (A -> B) -> List A -> List B

> rewards : (t : Nat) -> (x : X t) -> (y : Y t x) -> List Double
> rewards t x y = fmap (reward t x y) (step t x y)

> reduce : {A : Type} -> List (List A) -> List A
> reduce = concat -- library function that ``merges'' the lists together
