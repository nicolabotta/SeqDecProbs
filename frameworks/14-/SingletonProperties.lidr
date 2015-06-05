> module SingletonProperties


> import Data.Fin
> import Control.Isomorphism

> import Finite


> %default total


> ||| Mapping |()|s to |Fin|s
> toFin : () -> Fin (S Z)
> toFin () = FZ


> ||| Mapping |Fin (S Z)|s to |()|s
> fromFin : Fin (S Z) -> ()
> fromFin  FZ = ()
> fromFin (FS k) = absurd k


> ||| |toFin| is the left-inverse of |fromFin|
> toFinFromFinLemma : (k : Fin (S Z)) -> toFin (fromFin k) = k
> toFinFromFinLemma FZ = Refl
> toFinFromFinLemma (FS k) = absurd k


> ||| |fromFin| is the left-inverse of |toFin|
> fromFinToFinLemma : (e : ()) -> fromFin (toFin e) = e
> fromFinToFinLemma () = Refl


> ||| Singleton is finite
> finiteSingleton : Finite ()
> finiteSingleton = Evidence (S Z) iso where
>   iso : Iso () (Fin (S Z))
>   iso = MkIso toFin fromFin toFinFromFinLemma fromFinToFinLemma
