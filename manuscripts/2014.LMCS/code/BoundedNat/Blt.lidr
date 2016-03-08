> module Blt

> import Data.So
> import Data.Vect

> import Nat.Properties
> import Logic.Properties
> import Exists.Ops


> %default total

> %access public export



> Blt : Nat -> Type
> Blt b = (n : Nat ** LT n b)

> BltLemma0 : Blt Z -> alpha
> BltLemma0 (n ** p) = absurd p

> toNat : Blt b -> Nat
> toNat = outl

> toDouble : Blt b -> Double
> toDouble i = cast {from = Int} {to = Double} (cast {from = Nat} {to = Int} (Blt.toNat i))

> using (p : Nat -> Type)
>   Prelude.Show.Show (n : Nat ** p n) where
>     show (n ** _) = show n

> using (p : Nat -> Type)
>   Eq (n : Nat ** p n) where
>     (==) (n ** _) (n' ** _) = n == n'

> partial
> decBlt : Blt b -> Blt b
> decBlt {b} (S k ** q) = (k ** ltLemma1 k b q)

> incBlt : (n : Blt b) -> LT (S (Blt.toNat n)) b -> Blt b
> incBlt (k ** _) q = (S k ** q)

> toVect : {b : Nat} -> (Blt b -> a) -> Vect b a
> toVect {b = Z} _ = Nil
> toVect {b = S b'} {a = a} f = ((f (Z ** ltZS b')) :: toVect f') where
>   f' : Blt b' -> a
>   f' (k ** q) = f (S k ** LTESucc q)
