> module BoundedNat

> import Data.Fin
> import Data.Vect
> -- import Control.Isomorphism
> -- import Syntax.PreorderReasoning

> import BoundedNat
> import FinProperties
> import NatProperties
> import Sigma
> import PairsOperations


> %default total

> %access public export


> ||| Mapping bounded |Nat|s to |Fin|s
> toFin : {b : Nat} -> LTB b -> Fin b
> toFin {b = Z}   (MkSigma  _     nLT0        ) = void (succNotLTEzero nLT0)
> toFin {b = S m} (MkSigma  Z     _           ) = FZ
> toFin {b = S m} (MkSigma (S n) (LTESucc prf)) = FS (toFin (MkSigma n prf))

> ||| Mapping |Fin|s to bounded |Nat|s
> fromFin : {b : Nat} -> Fin b -> LTB b
> fromFin k = MkSigma (finToNat k) (finToNatLemma k)

> |||
> toVect : {b : Nat} -> {A : Type} -> (LTB b -> A) -> Vect b A
> toVect {b = Z}        _ = Nil
> toVect {b = S b'} {A} f = (f (MkSigma Z (ltZS b'))) :: toVect f' where
>   f' : LTB b' -> A
>   f' (MkSigma k q) = f (MkSigma (S k) (LTESucc q))
