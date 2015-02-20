> module BoundedNat

> import Data.Fin
> import Control.Isomorphism
> import Syntax.PreorderReasoning

> import BoundedNat
> import FinProperties


> %default total


> ||| Mapping bounded |Nat|s to |Fin|s
> toFin : (Sigma Nat (\ n => LT n b)) -> Fin b
> toFin {b = Z}   (_   ** nLT0)        = void (succNotLTEzero nLT0)
> toFin {b = S m} (Z   ** _)           = FZ
> toFin {b = S m} (S n ** LTESucc prf) = FS (toFin (n ** prf))


> ||| Mapping |Fin|s to bounded |Nat|s
> fromFin : Fin b -> (Sigma Nat (\ n => LT n b))
> fromFin k = (finToNat k ** finToNatLemma k)

