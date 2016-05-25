> module UnitProperties


> import Data.Fin
> import Control.Isomorphism

> import Finite
> import Sigma
> import PairsOperations


> %default total

> %access public export


> ||| Mapping |Unit|s to |Fin|s
> toFin : Unit -> Fin (S Z)
> toFin MkUnit = FZ


> ||| Mapping |Fin (S Z)|s to |Unit|s
> fromFin : Fin (S Z) -> Unit
> fromFin  FZ = MkUnit
> fromFin (FS k) = absurd k


> ||| |toFin| is the left-inverse of |fromFin|
> toFinFromFinLemma : (k : Fin (S Z)) -> toFin (fromFin k) = k
> toFinFromFinLemma FZ = Refl
> toFinFromFinLemma (FS k) = absurd k


> ||| |fromFin| is the left-inverse of |toFin|
> fromFinToFinLemma : (e : Unit) -> fromFin (toFin e) = e
> fromFinToFinLemma MkUnit = Refl


> ||| Unit is finite
> finiteUnit : Finite Unit
> finiteUnit = MkSigma (S Z) iso where
>   iso : Iso Unit (Fin (S Z))
>   iso = MkIso toFin fromFin toFinFromFinLemma fromFinToFinLemma
