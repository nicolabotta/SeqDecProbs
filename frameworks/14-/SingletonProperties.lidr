> module SingletonProperties


> import Data.Fin
> import Control.Isomorphism

> import Finite
> import Sigma
> import PairsOperations


> %default total

> %access public export


> ||| Mapping |()|s to |Fin|s
> toFin : Unit -> Fin (S Z)
> toFin () = FZ


> ||| Mapping |Fin (S Z)|s to |()|s
> fromFin : Fin (S Z) -> Unit
> fromFin  FZ = ()
> fromFin (FS k) = absurd k


> ||| |toFin| is the left-inverse of |fromFin|
> toFinFromFinLemma : (k : Fin (S Z)) -> toFin (fromFin k) = k
> toFinFromFinLemma FZ = Refl
> toFinFromFinLemma (FS k) = absurd k


> ||| |fromFin| is the left-inverse of |toFin|
> fromFinToFinLemma : (e : Unit) -> fromFin (toFin e) = e
> fromFinToFinLemma () = Refl


> ||| Singleton is finite
> finiteSingleton : Finite Unit
> finiteSingleton = MkSigma (S Z) iso where
>   iso : Iso Unit (Fin (S Z))
>   iso = MkIso toFin fromFin toFinFromFinLemma fromFinToFinLemma
