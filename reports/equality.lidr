> import Data.Fin


> %default total


> namespace Basics

>   cong2 : {alpha : Type} ->
>           {beta : Type} ->
>           {gamma : Type} ->
>           {a1 : alpha} ->
>           {a2 : alpha} ->
>           {b1 : beta} ->
>           {b2 : beta} ->
>           (f : alpha -> beta -> gamma) -> 
>           (a1 = a2) -> 
>           (b1 = b2) -> 
>           f a1 b1 = f a2 b2
>   cong2 f Refl Refl = Refl

>   depCong2 : {alpha : Type} -> 
>              {P : alpha -> Type} ->
>              {gamma : Type} ->
>              {a1 : alpha} -> 
>              {a2 : alpha} ->
>              {Pa1 : P a1} ->
>              {Pa2 : P a2} -> 
>              (f : (a : alpha) -> P a -> gamma) -> 
>              (a1 = a2) ->
>              (Pa1 = Pa2) -> 
>              f a1 Pa1 = f a2 Pa2
>   depCong2 f Refl Refl = Refl


> namespace NatProperties

>   instance Uninhabited (LTE (S n) Z) where
>     uninhabited LTEZero impossible
>     uninhabited (LTESucc x) impossible


> namespace FinProperties

>   finToNatLemma : (k : Fin n) -> LT (finToNat k) n 
>   finToNatLemma {n = Z}   k       =  absurd k
>   finToNatLemma {n = S m} FZ      =  LTESucc LTEZero 
>   finToNatLemma {n = S m} (FS k)  =  LTESucc (finToNatLemma k) 


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

> toFinLemma3 : (n : Nat) -> (b : Nat) -> (prf : LT n b) -> 
>               finToNatLemma (FS (toFin (n ** prf))) = LTESucc prf

> fromFin : Fin b -> (Sigma Nat (\ n => LT n b))
> fromFin k = (finToNat k ** finToNatLemma k)

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
>   s5 = ?kika -- depCong2 (MkSigma {a = Nat} {P = \ i => LT i (S m)}) s3 s4
>   s6 : fromFin (toFin (S n ** LTESucc prf)) = (S n ** LTESucc prf)
>   s6 = trans s1 (trans s2 s5)


