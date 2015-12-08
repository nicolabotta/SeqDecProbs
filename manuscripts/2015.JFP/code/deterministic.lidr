> module Deterministic

 
> %default total 


> X : (t : Nat) -> Type

> Y : (t : Nat) -> (x : X t) -> Type

> step : (t : Nat) -> (x : X t) -> (y : Y t x) -> X (S t)

> reward : (t : Nat) -> (x : X t) -> (y : Y t x) -> (x' : X (S t)) -> Double

> Pred : X t -> X (S t) -> Type
> Pred {t} x x'  =  Exists (\ y => x' = step t x y)

> Viable : (n : Nat) -> X t -> Type
> Viable {t}  Z    _  =  ()
> Viable {t} (S m) x  =  Exists (\ y => Viable m (step t x y))

> Reachable : X t' -> Type
> Reachable {t' =   Z} _   =  ()
> Reachable {t' = S t} x'  =  Exists (\ x => (Reachable x, x `Pred` x'))

> Policy : (t : Nat) -> (n : Nat) -> Type
> Policy t Z      =  Void
> -- Policy t (S m)  =  (x : X t) -> Viable (S m) x -> (y : Y t x ** Viable m (step t x y))
> Policy t (S m)  =  (x : X t) -> Reachable x -> Viable (S m) x -> (y : Y t x ** Viable m (step t x y))

> data PolicySeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  PolicySeq t Z
>   (::)  :  Policy t (S n) -> PolicySeq (S t) n -> PolicySeq t (S n)

