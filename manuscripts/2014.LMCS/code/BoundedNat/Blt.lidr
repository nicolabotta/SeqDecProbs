> module Blt


> import Nat.Postulates


> %default total


> Blt : Nat -> Type
> Blt b = (n : Nat ** so (n < b))

> toNat : Blt b -> Nat
> toNat = getWitness

> toFloat : Blt b -> Float
> toFloat = cast . (cast . (cast . Blt.toNat))

-- > (==) : Blt b -> Blt b -> Bool
-- > (==) i j = (toNat i == toNat j)

-- > class EqV a b where
-- >   eqv : a -> b -> Bool

-- > using (p : Nat -> Type)
-- >   instance Eq (n : Nat ** p n) where
-- >     (==) (n ** _) (n' ** _) = n == n'

-- > using (p : Nat -> Type)
-- >   instance Eq (n : Nat ** p n) where
-- >     (==) (n ** _) (n' ** _) = n == n'

> instance Eq (n : Nat ** so (n < b)) where
>   (==) (n ** a) (n' ** b) = n == n'

-- > instance Eq (Blt b) where
-- >   (==) (i ** _) (j ** _) = i == j

> partial
> decBlt : Blt b -> Blt b
> decBlt (S k ** q) = (k ** Sid_preserves_LT q)

> incBlt : (n : Blt b) -> so (S (Blt.toNat n) < b) -> Blt b
> incBlt (k ** _) q = (S k ** q)  

> toVect : {b : Nat} -> (Blt b -> a) -> Vect b a
> toVect {b = Z} _ = Nil
> toVect {b = S b'} {a = a} f = ((f (Z ** oh)) :: toVect f') where
>   f' : Blt b' -> a
>   f' (k ** q) = f (S k ** monotoneS q)  
  
