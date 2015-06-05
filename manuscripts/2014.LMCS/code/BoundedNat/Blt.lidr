> module Blt

> import Data.So
> import Data.Vect

> import Nat.Postulates
> import Logic.Properties
> import Exists.Ops


> %default total


> Blt : Nat -> Type
> Blt b = (n : Nat ** So (n < b))

> BltLemma0 : Blt Z -> alpha
> BltLemma0 (Z ** p)    =  soFalseElim p 
> BltLemma0 (S n ** p)  =  soFalseElim p 

> toNat : Blt b -> Nat
> toNat = outl

> toFloat : Blt b -> Float
> toFloat i = cast {from = Int} {to = Float} (cast {from = Nat} {to = Int} (Blt.toNat i))

> using (p : Nat -> Type)
>   instance Prelude.Show.Show (n : Nat ** p n) where
>     show (n ** _) = show n

> using (p : Nat -> Type)
>   instance Eq (n : Nat ** p n) where
>     (==) (n ** _) (n' ** _) = n == n'

> partial
> decBlt : Blt b -> Blt b
> decBlt (S k ** q) = (k ** Sid_preserves_LT q)

> incBlt : (n : Blt b) -> So (S (Blt.toNat n) < b) -> Blt b
> incBlt (k ** _) q = (S k ** q)  

> toVect : {b : Nat} -> (Blt b -> a) -> Vect b a
> toVect {b = Z} _ = Nil
> toVect {b = S b'} {a = a} f = ((f (Z ** Oh)) :: toVect f') where
>   f' : Blt b' -> a
>   f' (k ** q) = f (S k ** monotoneS q)  
  
