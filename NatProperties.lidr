> module NatProperties


> import Prop


> %default total


> instance Uninhabited (LTE (S n) Z) where
>   uninhabited LTEZero impossible
>   uninhabited (LTESucc x) impossible

> lteLemma1 : (m : Nat) -> (n : Nat) -> LTE (S m) n -> LTE m n
> lteLemma1  Z     Z             prf  = absurd prf
> lteLemma1  Z    (S n)  LTEZero        impossible
> lteLemma1  Z    (S n) (LTESucc prf) = LTEZero
> lteLemma1 (S m)  Z             prf  = absurd prf
> lteLemma1 (S m) (S n)  LTEZero        impossible
> lteLemma1 (S m) (S n) (LTESucc prf) = LTESucc (lteLemma1 m n prf)

> ltInLTE : (m : Nat) -> (n : Nat) -> LT m n -> LTE m n
> ltInLTE = lteLemma1 

