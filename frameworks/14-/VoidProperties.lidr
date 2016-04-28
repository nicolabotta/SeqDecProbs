> module VoidProperties


> import Data.Fin
> import Control.Isomorphism

> import Finite
> import Sigma


> %default total

> %access public export


> ||| Mapping |Void|s to |Fin|s
> toFin : Void -> Fin Z
> toFin = void


> ||| Mapping |Fin Z|s to |Void|s
> fromFin : Fin Z -> Void
> fromFin k = absurd k


> ||| |toFin| is the left-inverse of |fromFin|
> toFinFromFinLemma : (k : Fin Z) -> toFin (fromFin k) = k
> toFinFromFinLemma k = absurd k


> ||| |fromFin| is the left-inverse of |toFin|
> fromFinToFinLemma : (e : Void) -> fromFin (toFin e) = e
> fromFinToFinLemma e = void e


> ||| Void is finite
> finiteVoid : Finite Void
> finiteVoid = MkSigma Z iso where
>   iso : Iso Void (Fin Z)
>   iso = MkIso toFin fromFin toFinFromFinLemma fromFinToFinLemma


> {-

> ---}
