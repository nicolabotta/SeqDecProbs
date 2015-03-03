> module BoundedNat

> import Data.Fin
> import Data.Vect
> import Control.Isomorphism
> import Syntax.PreorderReasoning

> import BoundedNat
> import FinProperties
> import NatProperties


> %default total


> ||| Mapping bounded |Nat|s to |Fin|s
> toFin : {b : Nat} -> LTB b -> Fin b
> toFin {b = Z}   (_   ** nLT0)        = void (succNotLTEzero nLT0)
> toFin {b = S m} (Z   ** _)           = FZ
> toFin {b = S m} (S n ** LTESucc prf) = FS (toFin (n ** prf))


> ||| Mapping |Fin|s to bounded |Nat|s
> fromFin : {b : Nat} -> Fin b -> LTB b
> fromFin k = (finToNat k ** finToNatLemma k)


> |||
> toVect : {b : Nat} -> {A : Type} -> (LTB b -> A) -> Vect b A
> toVect {b = Z} _ = Nil
> toVect {b = S b'} {A} f = (f (Z ** ltZS b')) :: toVect f' where
>   f' : LTB b' -> A
>   f' (k ** q) = f (S k ** LTESucc q)  
