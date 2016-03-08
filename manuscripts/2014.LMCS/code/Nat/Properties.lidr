> module Properties

> import Data.So

> import Logic.Properties

> %default total

> %access public export


> -- Zero is not a successor
> ZnotS : Z = S n -> Void
> ZnotS Refl impossible

> -- A successor is not zero
> SnotZ : S n = Z -> Void
> SnotZ Refl impossible

> ltZ_bot : So (n < Z) -> Void
> ltZ_bot {n = Z}   nltZ  =  soFalseElim nltZ
> ltZ_bot {n = S m} nltZ  =  soFalseElim nltZ

> |||
> lteLemma1 : (m : Nat) -> (n : Nat) -> LTE (S m) n -> LTE m n
> lteLemma1  Z     Z             prf  = absurd prf
> lteLemma1  Z    (S n)  LTEZero        impossible
> lteLemma1  Z    (S n) (LTESucc prf) = LTEZero
> lteLemma1 (S m)  Z             prf  = absurd prf
> lteLemma1 (S m) (S n)  LTEZero        impossible
> lteLemma1 (S m) (S n) (LTESucc prf) = LTESucc (lteLemma1 m n prf)
> %freeze lteLemma1

> |||
> ltLemma1 : (m : Nat) -> (n : Nat) -> LT (S m) n -> LT m n
> ltLemma1 m n prf = lteLemma1 (S m) n prf
> %freeze ltLemma1

> |||
> idSuccPreservesLTE : (m : Nat) -> (n : Nat) -> m `LTE` n -> m `LTE` (S n)
> idSuccPreservesLTE  Z     n    prf = LTEZero
> idSuccPreservesLTE (S m)  Z    prf = absurd prf
> idSuccPreservesLTE (S m) (S n) prf = LTESucc (idSuccPreservesLTE m n (fromLteSucc prf))
> %freeze idSuccPreservesLTE

> |||
> idSuccPreservesLT : (m : Nat) -> (n : Nat) -> m `LT` n -> m `LT` (S n)
> idSuccPreservesLT  Z     n    prf = LTESucc LTEZero
> idSuccPreservesLT (S m)  Z    prf = absurd prf
> idSuccPreservesLT (S m) (S n) prf = LTESucc (idSuccPreservesLT m n (fromLteSucc prf))
> %freeze idSuccPreservesLT

> ||| Zero is smaller than any successor
> ltZS : (m : Nat) -> LT Z (S m)
> ltZS  Z    = LTESucc LTEZero
> ltZS (S m) = idSuccPreservesLTE (S Z) (S m) (ltZS m)
> %freeze ltZS

> ||| Any number is smaller than its successor
> ltIdS : (m : Nat) -> LT m (S m)
> ltIdS  Z    = LTESucc LTEZero
> ltIdS (S m) = LTESucc (ltIdS m)
> %freeze ltIdS

> ||| LTE is decidable
> decLTE : (m : Nat) -> (n : Nat) -> Dec (LTE m n)
> --decLTE = lte
> --{-
> decLTE Z _     = Yes LTEZero
> decLTE (S m) Z = No succNotLTEzero
> decLTE (S m) (S n) with (decLTE m n)
>   | (Yes p) = Yes (LTESucc p)
>   | (No contra) = No (\ p => contra (fromLteSucc p))
> ---}
> -- %freeze decLTE

> ||| LT is decidable
> decLT : (m : Nat) -> (n : Nat) -> Dec (LT m n)
> decLT m n = decLTE (S m) n
> %freeze decLT
