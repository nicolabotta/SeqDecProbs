> module NonNegQ


> %default total 

> -- %hide gcd


> succNotZ : Not (S n = Z)

> plusLemma1 : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Not (m + n = Z)

> multLemma1 : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Not (m * n = Z)

> gcd : Nat -> Nat -> Nat 
> gcd m  Z    = m 
> gcd m (S n) = assert_total (NonNegQ.gcd (S n) (modNatNZ m (S n) succNotZ))

> Divisor : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Type
> Divisor m n nmZ = modNatNZ n m nmZ = Z 

> divNatNZLemma1 : (m : Nat) -> (n : Nat) -> 
>                  (nmZ : Not (m = Z)) -> (nnZ : Not (n = Z)) -> Divisor n m nnZ ->
>                  Not (divNatNZ m n nnZ = Z)  

> gcdLemma1 : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Not (NonNegQ.gcd m n = Z)

> -- gcdLemma2 : (m : Nat) -> (n : Nat) -> (p : Not (gcd m n = Z)) -> Divisor (gcd m n) m p

> gcdLemma3 : (m : Nat) -> (n : Nat) -> (p : Not (gcd m n = Z)) -> Divisor (NonNegQ.gcd m n) n p

> Coprime : Nat -> Nat -> Type
> Coprime m n = NonNegQ.gcd m n = S Z

> gcdLemma4 : (m : Nat) -> (n : Nat) -> (nmZ : Not (m = Z)) -> (nnZ : Not (n = Z)) -> 
>             Coprime (divNatNZ m (gcd m n) (gcdLemma1 m n nmZ nnZ)) 
>                     (divNatNZ n (gcd m n) (gcdLemma1 m n nmZ nnZ))


Non-negative rational numbers:

> data NonNegQ  :  Type where
>   MkNonNegQ  :  (m : Nat) -> (n : Nat) -> Not (n = Z) -> Coprime m n -> NonNegQ

> plusNonNegQ : NonNegQ -> NonNegQ -> NonNegQ
> plusNonNegQ r (MkNonNegQ Z n2 p2 q2) = r
> plusNonNegQ (MkNonNegQ Z n1 p1 q1) s = s
> plusNonNegQ (MkNonNegQ (S m1) n1 p1 q1) (MkNonNegQ (S m2) n2 p2 q2) = MkNonNegQ m n p q where
>   n'     : Nat
>   n'     = n1 * n2
>   nn'Z   : Not (n' = Z)
>   nn'Z   = multLemma1 n1 n2 p1 p2
>   m'     : Nat
>   m'     = (S m1) * n2 + (S m2) * n1
>   nm'Z   : Not (m' = Z)
>   nm'Z   = plusLemma1 ((S m1) * n2) ((S m2) * n1) (multLemma1 (S m1) n2 succNotZ p2) (multLemma1 (S m2) n1 succNotZ p1)
>   gcd'   : Nat
>   gcd'   = NonNegQ.gcd m' n'
>   ngcd'Z : Not (gcd' = Z)
>   ngcd'Z = gcdLemma1 m' n' nm'Z nn'Z
>   m      : Nat
>   m      = divNatNZ m' gcd' ngcd'Z
>   n      : Nat
>   n      = divNatNZ n' gcd' ngcd'Z
>   p      : Not (n = Z)
>   p      = divNatNZLemma1 n' gcd' nn'Z ngcd'Z (gcdLemma3 m' n' ngcd'Z)
>   q      : Coprime m n
>   q      = gcdLemma4 m' n' nm'Z nn'Z


--

> --{-

> instance Show NonNegQ where
>   show (MkNonNegQ m n p q) = "frac " ++ show m ++ " " ++ show n

> numerator : NonNegQ -> Nat
> numerator (MkNonNegQ m n p q) = m 

> denominator : NonNegQ -> Nat
> denominator (MkNonNegQ m n p q) = n

> gcdLemma1 m  Z    p q h = p h
> gcdLemma1 m (S n) p q h with (decEq (modNatNZ m (S n) succNotZ) Z)
>   gcdLemma1 m (S n) p q h | (Yes prf)   = res h where
>                              s1  : NonNegQ.gcd m (S n) = NonNegQ.gcd (S n) (modNatNZ m (S n) succNotZ)
>                              s1  = Refl
>                              s2  : NonNegQ.gcd m (S n) = NonNegQ.gcd (S n) Z
>                              s2  = replace {P = \ z => NonNegQ.gcd m (S n) = NonNegQ.gcd (S n) z} prf s1
>                              s3  : NonNegQ.gcd (S n) Z = S n
>                              s3  = Refl
>                              s4  : NonNegQ.gcd m (S n) = S n
>                              s4  = trans s2 s3
>                              res : Not (NonNegQ.gcd m (S n) = Z)
>                              res = \ k => succNotZ (trans (sym s4) k)
>   gcdLemma1 m (S n) p q h | (No contra) = res h where
>                              m' : Nat
>                              m' = S n
>                              n' : Nat
>                              n' = modNatNZ m (S n) succNotZ
>                              p' : Not (m' = Z)
>                              p' = succNotZ
>                              q' : Not (n' = Z)
>                              q' = contra
>                              res : Not (NonNegQ.gcd (S n) (modNatNZ m (S n) succNotZ) = Z)
>                              res = assert_total (gcdLemma1 m' n' p' q')

> succNotZ Refl impossible

> ---}
