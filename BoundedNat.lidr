> module BoundedNat

> import Data.Fin
> import Control.Isomorphism

> import Basics
> import NatProperties
> import SigmaProperties
> import FinProperties
> import Finite


> %default total


> LTB : Nat -> Type
> LTB b = Sigma Nat (\ n  => LT n b)

> instance Uninhabited (LTB Z) where
>   uninhabited (n ** prf) = absurd prf


> toFin : (Sigma Nat (\ n => LT n b)) -> Fin b
> toFin {b = Z}   (_   ** nLT0)        = void (succNotLTEzero nLT0)
> toFin {b = S m} (Z   ** _)           = FZ
> toFin {b = S m} (S n ** LTESucc prf) = FS (toFin (n ** prf))

> toFinLemma0 : (n : Nat) -> (b : Nat) -> (prf : LT n b) -> 
>               finToNat (toFin (n ** prf)) = n
> toFinLemma0   n     Z             prf = absurd prf
> toFinLemma0   Z    (S a) (LTESucc prf) = Refl
> toFinLemma0  (S m) (S a) (LTESucc prf) = 
>   let ih = toFinLemma0 m a prf in rewrite ih in Refl

> toFinLemma1 : (n : Nat) -> (b : Nat) -> (prf : LT n b) -> 
>               finToNat (FS (toFin (n ** prf))) = S n
> toFinLemma1 n b prf = trans s1 s2 where
>   s1 : finToNat (FS (toFin (n ** prf)))
>        =
>        S (finToNat (toFin (n ** prf)))
>   s1 = Refl
>   s2 : S (finToNat (toFin (n ** prf)))
>        =
>        S n
>   s2 = cong (toFinLemma0 n b prf)

> toFinLemma2 : (n : Nat) -> (b : Nat) -> (prf : LT n b) -> 
>               finToNatLemma (toFin (n ** prf)) = prf
> toFinLemma2   n     Z     prf              = absurd prf
> toFinLemma2   Z    (S b) (LTESucc LTEZero) = Refl
> toFinLemma2  (S n) (S b) (LTESucc prf) = trans s1 (trans s2 s4) where
>   s1 : finToNatLemma (toFin (S n ** LTESucc prf))
>        =
>        finToNatLemma (FS (toFin (n ** prf)))
>   s1 = Refl
>   s2 : finToNatLemma (FS (toFin (n ** prf)))
>        =
>        LTESucc (finToNatLemma (toFin (n ** prf)))
>   s2 = Refl
>   s3 : finToNatLemma (toFin (n ** prf))
>        =
>        prf
>   s3 = toFinLemma2 n b prf
>   s4 : LTESucc (finToNatLemma (toFin (n ** prf)))
>        =
>        LTESucc prf
>   s4 = depCong2' {alpha = Nat}
>                  {P = \ n => LT n b}
>                  {Q = \ n, prf => LT (S n) (S b)}
>                  {a1 = finToNat (toFin (n ** prf))}
>                  {a2 = n}
>                  {Pa1 = finToNatLemma (toFin (n ** prf))}
>                  {Pa2 = prf}
>                  (\ n, prf => LTESucc prf)
>                  (toFinLemma0 n b prf)
>                  s3

> toFinLemma3 : (n : Nat) -> (b : Nat) -> (prf : LT n b) -> 
>               finToNatLemma (FS (toFin (n ** prf))) = LTESucc prf
> toFinLemma3 n b prf = trans s1 s2 where
>   s0 : FS (toFin (n ** prf)) = toFin (S n ** LTESucc prf)
>   s0 = Refl
>   s1 : finToNatLemma (FS (toFin (n ** prf))) 
>        = 
>        finToNatLemma (toFin (S n ** LTESucc prf))
>   s1 = replace {a = Fin (S b)} 
>                {x = FS (toFin (n ** prf))} 
>                {y = toFin (S n ** LTESucc prf)} 
>                {P = \ x => finToNatLemma (FS (toFin (n ** prf))) = finToNatLemma x} 
>                s0 Refl
>   s2 : finToNatLemma (toFin (S n ** LTESucc prf))
>        =
>        LTESucc prf
>   s2 = toFinLemma2 (S n) (S b) (LTESucc prf)

> fromFin : Fin b -> (Sigma Nat (\ n => LT n b))
> fromFin k = (finToNat k ** finToNatLemma k)

> toFinFromFinLemma : (k : Fin b) -> toFin (fromFin k) = k
> toFinFromFinLemma {b = Z} k = absurd k
> toFinFromFinLemma {b = S m} FZ = Refl
> toFinFromFinLemma {b = S m} (FS k) =
>   let ih = toFinFromFinLemma k in
>   rewrite ih in
>   Refl

> fromFinToFinLemma : (n : LTB b) -> fromFin (toFin n) = n
> fromFinToFinLemma {b = Z}   m = absurd m
> fromFinToFinLemma {b = S m} (Z ** LTESucc LTEZero) = Refl
> fromFinToFinLemma {b = S m} (S n ** LTESucc prf) = s6 where
>   s1 : fromFin (toFin (S n ** LTESucc prf))
>        =
>        fromFin (FS (toFin (n ** prf)))
>   s1 = Refl
>   s2 : fromFin (FS (toFin (n ** prf)))
>        =
>        (finToNat (FS (toFin (n ** prf))) ** finToNatLemma (FS (toFin (n ** prf))))
>   s2 = Refl
>   s3 : finToNat (FS (toFin (n ** prf))) = S n
>   s3 = toFinLemma1 n m prf
>   s4 : finToNatLemma (FS (toFin (n ** prf))) = LTESucc prf
>   s4 = toFinLemma3 n m prf
>   s5 : MkSigma {a = Nat} {P = \ i => LT i (S m)} 
>        (finToNat (FS (toFin (n ** prf)))) 
>        (finToNatLemma (FS (toFin (n ** prf))))
>        = 
>        MkSigma {a = Nat} {P = \ i => LT i (S m)} (S n) (LTESucc prf)
>   s5 = depCong2 (MkSigma {a = Nat} {P = \ i => LT i (S m)}) s3 s4
>   s6 : fromFin (toFin (S n ** LTESucc prf)) = (S n ** LTESucc prf)
>   s6 = trans s1 (trans s2 s5)


> finiteLTB : (b : Nat) -> Finite (LTB b)
> finiteLTB b = Evidence b iso where
>   iso : Iso (LTB b) (Fin b)
>   iso = MkIso toFin fromFin toFinFromFinLemma fromFinToFinLemma


> {-

> BltLemma0 : Blt Z -> alpha
> BltLemma0 (Z ** p)    =  soFalseElim p 
> BltLemma0 (S n ** p)  =  soFalseElim p 

> toNat : Blt b -> Nat
> toNat = outl

> toFloat : Blt b -> Float
> toFloat = cast . (cast . (cast . Blt.toNat))

-- > (==) : Blt b -> Blt b -> Bool
-- > (==) i j = (toNat i == toNat j)

> using (p : Nat -> Type)
>   instance Show (n : Nat ** p n) where
>     show (n ** _) = show n

> using (p : Nat -> Type)
>   instance Eq (n : Nat ** p n) where
>     (==) (n ** _) (n' ** _) = n == n'

> decBlt : (i : Blt b) -> (p : Blt.toNat i = S m) -> Blt b
> decBlt (S k ** q) Refl = (k ** Sid_preserves_LT q)
> decBlt (  Z ** q) Refl impossible

> incBlt : (n : Blt b) -> So (S (Blt.toNat n) < b) -> Blt b
> incBlt (k ** _) q = (S k ** q)  

> toVect : {b : Nat} -> (Blt b -> a) -> Vect b a
> toVect {b = Z} _ = Nil
> toVect {b = S b'} {a = a} f = ((f (Z ** Oh)) :: toVect f') where
>   f' : Blt b' -> a
>   f' (k ** q) = f (S k ** monotoneS q)  
  
> -}
