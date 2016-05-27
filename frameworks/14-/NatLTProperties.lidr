> module NatLTProperties

> import NatBasicProperties
> import NatLTEProperties


> %default total
> %access public export
> %auto_implicits on


|LT| is unique:

> ||| LT is unique
> uniqueLT : (p1 : LT m n) -> (p2 : LT m n) -> p1 = p2
> uniqueLT {m} {n} = uniqueLTE {m = S m} {n = n}
> %freeze uniqueLT

> |||
> uniqueLT' : m1 = m2 -> n1 = n2 -> (p1 : LT m1 n1) -> (p2 : LT m2 n2) -> p1 = p2
> uniqueLT' Refl Refl p1 p2 = uniqueLT p1 p2
> %freeze uniqueLT'


|LT| is decidable:

> ||| LT is decidable
> decLT : (m : Nat) -> (n : Nat) -> Dec (LT m n)
> decLT m n = decLTE (S m) n
> %freeze decLT


Properties of |LT| and successor:

> |||
> ltLemma1 : (m : Nat) -> (n : Nat) -> LT (S m) n -> LT m n
> ltLemma1 m n prf = lteLemma1 (S m) n prf
> %freeze ltLemma1

> ||| LT is contained in LTE
> ltInLTE : (m : Nat) -> (n : Nat) -> LT m n -> LTE m n
> ltInLTE = lteLemma1
> %freeze ltInLTE

> ||| Zero is smaller than any successor
> ltZS : (m : Nat) -> LT Z (S m)
> ltZS  Z    = LTESucc LTEZero
> ltZS (S m) = idSuccPreservesLTE (S Z) (S m) (ltZS m)
> %freeze ltZS

> ||| Zero is smaller than any successor
> ltZS' : {n : Nat} -> LT Z (S n)
> ltZS' {n = Z}   = LTESucc LTEZero
> ltZS' {n = S m} = idSuccPreservesLTE (S Z) (S m) ltZS'
> %freeze ltZS'

> ||| Any number is smaller than its successor
> ltIdS : (m : Nat) -> LT m (S m)
> ltIdS  Z    = LTESucc LTEZero
> ltIdS (S m) = LTESucc (ltIdS m)
> %freeze ltIdS

> ||| Any number which is not zero is greater than zero
> notZisgtZ : {n : Nat} -> Not (n = Z) -> LT Z n
> notZisgtZ {n = Z}   contra = void (contra Refl)
> notZisgtZ {n = S m} _      = ltZS m
> %freeze notZisgtZ

> ||| Any number which is greater than zero is not zero
> gtZisnotZ : {n : Nat} -> LT Z n -> Not (n = Z)
> gtZisnotZ {n = Z}   p = absurd p
> gtZisnotZ {n = S m} p = SIsNotZ 
> %freeze gtZisnotZ

> ||| No number is less than zero
> notLTzero : {n : Nat} -> Not (LT n Z)
> notLTzero = succNotLTEzero
> %freeze notLTzero

> |||
> strengthenLT : (m : Nat) -> (n : Nat) -> LT m (S n) -> Not (m = n) -> LT m n
> strengthenLT  Z       n  _       zNEQn   = notZisgtZ (zNEQn . sym)
> strengthenLT (S m)  Z    smLTsz  _       = void (notLTzero (fromLteSucc smLTsz))
> strengthenLT (S m) (S n) smLTssn smNEQsn = LTESucc mLTn where
>   mLTsn : LT m (S n)
>   mLTsn = fromLteSucc smLTssn
>   mNEQn : Not (m = n)
>   mNEQn = predInjective m n smNEQsn
>   mLTn : LT m n
>   mLTn = strengthenLT m n mLTsn mNEQn
> %freeze strengthenLT


> {-

> ---}
