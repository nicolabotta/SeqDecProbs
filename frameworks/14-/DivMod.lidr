> module DivMod

> import Data.Nat.DivMod
> import Syntax.PreorderReasoning

> %default total
> %hide gcd
> %hide divNatNZ
> %hide modNatNZ


* Nat lemmas (to be implemented in a separate module):

> |||
> postulate plusZfstZ : (m : Nat) -> (n : Nat) -> m + n = Z -> m = Z

> |||
> postulate plusZsndZ : (m : Nat) -> (n : Nat) -> m + n = Z -> n = Z

> |||
> postulate multZfstZ : (m : Nat) -> (n : Nat) -> m * n = Z -> Not (n = Z) -> m = Z

> |||
> postulate multNZfst : (m : Nat) -> (n : Nat) -> Not (m * n = Z) -> Not (m = Z)

> |||
> postulate multNZsnd : (m : Nat) -> (n : Nat) -> Not (m * n = Z) -> Not (n = Z)

> ||| Multiplication times S (S m) increases
> postulate multSSNotLTE : (m : Nat) -> (n : Nat) -> Not (n = Z) -> Not ((S (S m)) * n `LTE` n)

> |||
> postulate eqMultRight : (m1 : Nat) -> (m2 : Nat) -> (n : Nat) -> m1 = m2 -> m1 * n = m2 * n

> |||
> -- postulate multNZNZNZ : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Not (m * n = Z)

> |||
> postulate ltOneIsZ : (m : Nat) -> m `LT` (S Z) -> m = Z

> |||
> postulate oneLTNotZ : (m : Nat) -> (S Z) `LTE` m -> Not (m = Z)

> |||
> postulate lteAntisymmetric : (m : Nat) -> (n : Nat) -> m `LTE` n -> n `LTE` m -> m = n


* Quotient and remainder

** Specification:

> ||| The quotient of m / n
> divNatNZ : (m : Nat) -> (n : Nat) -> Not (n = Z) -> Nat

> ||| The remainder of m / n
> modNatNZ : (m : Nat) -> (n : Nat) -> Not (n = Z) -> Nat

> ||| The sum of remainder of m / n and quotient of m / n times n is m
> divmodNatNZSpec0 : (m : Nat) -> (n : Nat) -> (p : Not (n = Z)) ->
>                    modNatNZ m n p + (divNatNZ m n p) * n = m

> ||| The remainder of m / n is smaller than n
> divmodNatNZSpec1 : (m : Nat) -> (n : Nat) -> (p : Not (n = Z)) ->
>                    modNatNZ m n p `LT` n

** Implementation (after Melvar Chen):

> |||
> divmodNatNZ : (m : Nat) -> (n : Nat) -> Not (n = Z) -> (Nat, Nat)
> divmodNatNZ m  Z    p = void (p Refl)
> divmodNatNZ m (S n) p with (divMod m n)
>   divmodNatNZ (r + q * (S n)) (S n) p | MkDivMod q r rLTSn = (q, r)

> divNatNZ m n nnZ = fst (divmodNatNZ m n nnZ)

> modNatNZ m n nnZ = snd (divmodNatNZ m n nnZ)

> divmodNatNZSpec0 m  Z    p = void (p Refl)
> divmodNatNZSpec0 m (S n) p with (divMod m n)
>   divmodNatNZSpec0 (r + q * (S n)) (S n) p | MkDivMod q r rLTn = Refl

> divmodNatNZSpec1 m  Z    p = void (p Refl)
> divmodNatNZSpec1 m (S n) p with (divMod m n)
>   divmodNatNZSpec1 (r + q * (S n)) (S n) p | MkDivMod q r rLTn = rLTn

** Properties (implementation dependent)

** Properties (implementation independent)

> divmodNatNZLemma0 : (m : Nat) -> (n : Nat) -> (p : Not (n = Z)) ->
>                     modNatNZ m n p = Z -> (divNatNZ m n p) * n = m
> divmodNatNZLemma0 m n p modZ = s3 where
>   s1 : modNatNZ m n p + (divNatNZ m n p) * n = m
>   s1 = divmodNatNZSpec0 m n p
>   s2 : Z + (divNatNZ m n p) * n = m
>   s2 = replace {x = modNatNZ m n p}
>                {y = Z}
>                {P = \ ZUZU => ZUZU + (divNatNZ m n p) * n = m}
>                modZ s1
>   s3 : (divNatNZ m n p) * n = m
>   s3 = replace {x = Z + (divNatNZ m n p) * n}
>                {y = (divNatNZ m n p) * n}
>                {P = \ ZUZU => ZUZU = m}
>                (plusZeroLeftNeutral ((divNatNZ m n p) * n)) s2

> -- divmodNatNZLemma1 : (m : Nat) -> (n : Nat) -> (p : Not (n = Z)) ->
> --                     (divNatNZ m n p) * n = m -> modNatNZ m n p = Z

> ||| The quotient of Z / n is Z
> divNatNZLemma0 : (n : Nat) -> (p : Not (n = Z)) -> divNatNZ Z n p = Z
> divNatNZLemma0 n p = s1 where
>   s0 : (divNatNZ Z n p) * n = Z
>   s0 = plusZsndZ (modNatNZ Z n p) ((divNatNZ Z n p) * n) (divmodNatNZSpec0 Z n p)
>   s1 : divNatNZ Z n p = Z
>   s1 = multZfstZ (divNatNZ Z n p) n s0 p

> ||| The remainder of Z / n is Z
> modNatNZLemma0 : (n : Nat) -> (p : Not (n = Z)) -> modNatNZ Z n p = Z
> modNatNZLemma0 n p = plusZfstZ (modNatNZ Z n p)
>                                ((divNatNZ Z n p) * n)
>                                (divmodNatNZSpec0 Z n p)

> |||
> modNatNZLemma1 : (m : Nat) -> (p : Not (S Z = Z)) -> modNatNZ m (S Z) p = Z
> modNatNZLemma1 m p = s2 where
>   s1 : modNatNZ m (S Z) p `LT` (S Z)
>   s1 = divmodNatNZSpec1 m (S Z) p
>   s2 : modNatNZ m (S Z) p = Z
>   s2 = ltOneIsZ (modNatNZ m (S Z) p) s1

> |||
> divNatNZLemma1 : (m : Nat) -> (p : Not (S Z = Z)) -> divNatNZ m (S Z) p = m
> divNatNZLemma1 m p = s2 where
>   s1 : (divNatNZ m (S Z) p) * (S Z) = m
>   s1 = divmodNatNZLemma0 m (S Z) p (modNatNZLemma1 m p)
>   s2 : divNatNZ m (S Z) p = m
>   s2 = replace {x = (divNatNZ m (S Z) p) * (S Z)}
>                {y = divNatNZ m (S Z) p}
>                {P = \ ZUZU => ZUZU = m}
>                (multOneRightNeutral (divNatNZ m (S Z) p)) s1

> |||
> -- divNatNZLemma2 : (m : Nat) -> Not (m = Z) -> divNatNZ m m p = S Z

> |||
> divNatNZLemma3 : (m : Nat) -> (n : Nat) -> (nmZ : Not (m = Z)) ->
>                  (divNatNZ n m nmZ) * m = n ->
>                  (q : Nat) -> (nmqZ : Not (m * q = Z)) ->
>                  (divNatNZ (n * q) (m * q) nmqZ) * m = n


* Divisor relation

** Specification:

> Divisor : (m : Nat) -> (n : Nat) -> Type

> divisorSpec1 : (m : Nat) -> (n : Nat) -> m `Divisor` n ->
>                (p : Not (m = Z)) -> (divNatNZ n m p) * m = n

** Implementation:

> Divisor m n = (p : Not (m = Z)) -> (divNatNZ n m p) * m = n

> divisorSpec1 m n = id

** Properties (implementation dependent)

> divisorLemma2 : (m : Nat) -> (n : Nat) -> m `Divisor` n ->
>                 (q : Nat) -> (m * q) `Divisor` (n * q)
> divisorLemma2 m n mdn q nmqZ = s4 where
>   nmZ : Not (m = Z)
>   nmZ = multNZfst m q nmqZ
>   nqZ : Not (q = Z)
>   nqZ = multNZsnd m q nmqZ
>   s1 : (divNatNZ n m nmZ) * m = n
>   s1 = mdn nmZ
>   s2 : (divNatNZ (n * q) (m * q) nmqZ) * m = n
>   s2 = divNatNZLemma3 m n nmZ s1 q nmqZ
>   s3 : (divNatNZ (n * q) (m * q) nmqZ) * m * q = n * q
>   s3 = eqMultRight ((divNatNZ (n * q) (m * q) nmqZ) * m) n q s2
>   s4 : (divNatNZ (n * q) (m * q) nmqZ) * (m * q) = n * q
>   s4 = replace {x = (divNatNZ (n * q) (m * q) nmqZ) * m * q}
>                {y = (divNatNZ (n * q) (m * q) nmqZ) * (m * q)}
>                {P = \ ZUZU => ZUZU = n * q}
>                (sym (multAssociative (divNatNZ (n * q) (m * q) nmqZ) m q)) s3

> divisorLemma3 : (m : Nat) -> (S Z) `Divisor` m
> divisorLemma3 m p = divmodNatNZLemma0 m (S Z) p (modNatNZLemma1 m p)

** Properties (implementation independent)

> divisorLemma1 : (m : Nat) -> (n : Nat) -> m `Divisor` n ->
>                 (p : Not (m = Z)) -> modNatNZ n m p = Z
> divisorLemma1 m n mdn p = s4 where
>   s1 : modNatNZ n m p + (divNatNZ n m p) * m = n
>   s1 = divmodNatNZSpec0 n m p
>   s2 : modNatNZ n m p + n = n
>   s2 = replace {x = (divNatNZ n m p) * m}
>                {y = n}
>                {P = \ ZUZU => modNatNZ n m p + ZUZU = n}
>                (divisorSpec1 m n mdn p)
>                s1
>   s3 : n + modNatNZ n m p = n
>   s3 = replace {x = modNatNZ n m p + n}
>                {y = n + modNatNZ n m p}
>                {P = \ ZUZU => ZUZU = n}
>                (plusCommutative (modNatNZ n m p) n)
>                s2
>   s4 : modNatNZ n m p = Z
>   s4 = plusLeftLeftRightZero n (modNatNZ n m p) s3


* Greatest common divisor

** Specification:

> ||| The greatest common divisor of m and n
> gcd : (m : Nat) -> (n : Nat) -> Nat

> ||| gcd id commutative
> %assert_total
> gcdSpec0 : (m : Nat) -> (n : Nat) -> gcd m n = gcd n m

> ||| gcd m n is a divisor of m
> gcdSpec1 : (m : Nat) -> (n : Nat) -> (gcd m n) `Divisor` m

> ||| gcd m n is a divisor of n
> gcdSpec2 : (m : Nat) -> (n : Nat) -> (gcd m n) `Divisor` n

> ||| gcd m n is the greatest divisor of m n
> gcdSpec3 : (m : Nat) -> (n : Nat) -> (d : Nat) ->
>             d `Divisor` m -> d `Divisor` n -> Not (m = Z) -> Not (n = Z) ->
>             d `LTE` gcd m n

** Implementation:

> gcd m  Z    = m
> gcd m (S n) = assert_total (gcd (S n) (modNatNZ m (S n) SIsNotZ))

> mutual

>   gcdSpec0  Z     Z    = Refl
>
>   gcdSpec0  Z    (S n) =
>       ( gcd (S n) (modNatNZ Z (S n) SIsNotZ) )
>     ={ replace {x = modNatNZ Z (S n) SIsNotZ}
>                {y = Z}
>                {P = \ ZUZU => gcd (S n) (modNatNZ Z (S n) SIsNotZ) = gcd (S n) ZUZU}
>                (modNatNZLemma0 (S n) SIsNotZ)
>                Refl }=
>       ( gcd (S n) Z )
>     QED
>
>   gcdSpec0 (S m)  Z    =
>       ( gcd (S m) Z )
>     ={ replace {x = Z}
>                {y = modNatNZ Z (S m) SIsNotZ}
>                {P = \ ZUZU => gcd (S m) Z = gcd (S m) ZUZU}
>                (sym (modNatNZLemma0 (S m) SIsNotZ))
>                Refl }=
>       ( gcd (S m) (modNatNZ Z (S m) SIsNotZ) )
>     ={ Refl }=
>       ( gcd Z (S m) )
>     QED
>
>   gcdSpec0 (S m) (S n) = s7 where
>     s1 : (gcd (S n) (S m)) `Divisor` (S n)
>     s1 = gcdSpec1 (S n) (S m)
>     s2 : (gcd (S n) (S m)) `Divisor` (S m)
>     s2 = gcdSpec2 (S n) (S m)
>     s3 : (gcd (S m) (S n)) `Divisor` (S m)
>     s3 = gcdSpec1 (S m) (S n)
>     s4 : (gcd (S m) (S n)) `Divisor` (S n)
>     s4 = gcdSpec2 (S m) (S n)
>     s5 : (gcd (S n) (S m)) `LTE` (gcd (S m) (S n))
>     s5 = gcdSpec3 (S m) (S n) (gcd (S n) (S m)) s2 s1 SIsNotZ SIsNotZ
>     s6 : (gcd (S m) (S n)) `LTE` (gcd (S n) (S m))
>     s6 = gcdSpec3 (S n) (S m) (gcd (S m) (S n)) s4 s3 SIsNotZ SIsNotZ
>     s7 : gcd (S m) (S n) = gcd (S n) (S m)
>     s7 = lteAntisymmetric (gcd (S m) (S n)) (gcd (S n) (S m)) s6 s5

>   gcdSpec1 m n = s2 where
>     s1 : (gcd n m) `Divisor` m
>     s1 = gcdSpec2 n m
>     s2 : (gcd m n) `Divisor` m
>     s2 = replace {x = gcd n m} {y = gcd m n} {P = \ ZUZU => ZUZU `Divisor` m} (gcdSpec0 n m) s1

>   gcdSpec2 m  Z    = s4 where
>     s1 : (p : Not (m = Z)) -> modNatNZ Z m p + (divNatNZ Z m p) * m = Z
>     s1 p = divmodNatNZSpec0 Z m p
>     s2 : (p : Not (m = Z)) ->              Z + (divNatNZ Z m p) * m = Z
>     s2 p = replace {x = modNatNZ Z m p}
>                    {y = Z}
>                    {P = \ ZUZU => ZUZU + (divNatNZ Z m p) * m = Z}
>                    (modNatNZLemma0 m p)
>                    (s1 p)
>     s3 : (p : Not (m = Z)) -> (divNatNZ Z m p) * m = Z
>     s3 p = replace {x = Z + (divNatNZ Z m p) * m}
>                    {y = (divNatNZ Z m p) * m}
>                    {P = \ ZUZU => ZUZU = Z}
>                    (plusZeroLeftNeutral ((divNatNZ Z m p) * m))
>                    (s2 p)
>     s4 : m `Divisor` Z
>     s4 = s3
>   gcdSpec2 m (S n) = s1 where
>     s1 : (gcd (S n) (modNatNZ m (S n) SIsNotZ)) `Divisor` (S n)
>     s1 = assert_total (gcdSpec1 (S n) (modNatNZ m (S n) SIsNotZ))

** Properties (implementation dependent)

> gcdOneRightOne : (n : Nat) -> gcd (S Z) n = S Z
> gcdOneRightOne n =
>     ( gcd (S Z) n )
>   ={ gcdSpec0 (S Z) n }=
>     ( gcd n (S Z) )
>   ={ Refl }=
>     ( gcd (S Z) (modNatNZ n (S Z) SIsNotZ) )
>   ={ replace {x = modNatNZ n (S Z) SIsNotZ}
>              {y = Z}
>              {P = \ ZUZU => gcd (S Z) (modNatNZ n (S Z) SIsNotZ) = gcd (S Z) ZUZU}
>              (modNatNZLemma1 n SIsNotZ)
>              Refl }=
>     ( gcd (S Z) Z )
>   ={ Refl }=
>     ( S Z )
>   QED

** Properties (implementation independent)

> gcdLemma1 : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Not (gcd m n = Z)
> gcdLemma1 m n nmZ nnZ = s4 where
>   s1 : (S Z) `Divisor` m
>   s1 = divisorLemma3 m
>   s2 : (S Z) `Divisor` n
>   s2 = divisorLemma3 n
>   s3 : (S Z) `LTE` (gcd m n)
>   s3 = gcdSpec3 m n (S Z) s1 s2 nmZ nnZ
>   s4 : Not (gcd m n = Z)
>   s4 = oneLTNotZ (gcd m n) s3

> gcdLemma2 : (m : Nat) -> (n : Nat) -> (nmZ : Not (m = Z)) -> (nnZ : Not (n = Z)) ->
>             Not (divNatNZ m (gcd m n) (gcdLemma1 m n nmZ nnZ) = Z)
> gcdLemma2 m n nmZ nnZ = s3 where
>   s1 : (divNatNZ m (gcd m n) (gcdLemma1 m n nmZ nnZ)) * (gcd m n) = m
>   s1 = gcdSpec1 m n (gcdLemma1 m n nmZ nnZ)
>   s2 : Not ((divNatNZ m (gcd m n) (gcdLemma1 m n nmZ nnZ)) * (gcd m n) = Z)
>   s2 = replace {x = m}
>                {y = (divNatNZ m (gcd m n) (gcdLemma1 m n nmZ nnZ)) * (gcd m n)}
>                {P = \ ZUZU => Not (ZUZU = Z)}
>                (sym s1)
>                nmZ
>   s3 : Not (divNatNZ m (gcd m n) (gcdLemma1 m n nmZ nnZ) = Z)
>   s3 = multNZfst (divNatNZ m (gcd m n) (gcdLemma1 m n nmZ nnZ)) (gcd m n) s2

> gcdLemma3 : (m : Nat) -> (n : Nat) -> (nmZ : Not (m = Z)) -> (nnZ : Not (n = Z)) ->
>             Not (divNatNZ n (gcd m n) (gcdLemma1 m n nmZ nnZ) = Z)
> gcdLemma3 m n nmZ nnZ = s3 where
>   s1 : (divNatNZ n (gcd m n) (gcdLemma1 m n nmZ nnZ)) * (gcd m n) = n
>   s1 = gcdSpec2 m n (gcdLemma1 m n nmZ nnZ)
>   s2 : Not ((divNatNZ n (gcd m n) (gcdLemma1 m n nmZ nnZ)) * (gcd m n) = Z)
>   s2 = replace {x = n}
>                {y = (divNatNZ n (gcd m n) (gcdLemma1 m n nmZ nnZ)) * (gcd m n)}
>                {P = \ ZUZU => Not (ZUZU = Z)}
>                (sym s1)
>                nnZ
>   s3 : Not (divNatNZ n (gcd m n) (gcdLemma1 m n nmZ nnZ) = Z)
>   s3 = multNZfst (divNatNZ n (gcd m n) (gcdLemma1 m n nmZ nnZ)) (gcd m n) s2

* Operations

> reduceFst : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Nat
> reduceFst m n nmZ nnZ = divNatNZ m (gcd m n) (gcdLemma1 m n nmZ nnZ)

> reduceSnd : (m : Nat) -> (n : Nat) -> Not (m = Z) -> Not (n = Z) -> Nat
> reduceSnd m n nmZ nnZ = divNatNZ n (gcd m n) (gcdLemma1 m n nmZ nnZ)


* Coprime

> ||| m `Coprime` n <=> gcd m n = S Z
> Coprime : Nat -> Nat -> Type
> Coprime m n = gcd m n = S Z

** Properties

> coprimeCommutative : (m : Nat) -> (n : Nat) -> Coprime m n = Coprime n m
> coprimeCommutative m n =
>     ( gcd m n = S Z )
>   ={ replace {x = gcd m n} {y = gcd n m} {P = \ ZUZU => (gcd m n = S Z) = (ZUZU = S Z)} (gcdSpec0 m n) Refl }=
>     ( gcd n m = S Z )
>   QED

> oneCoprime : (m : Nat) -> Coprime (S Z) m
> oneCoprime = gcdOneRightOne

> coprimeReduce : (m : Nat) -> (n : Nat) -> (nmZ : Not (m = Z)) -> (nnZ : Not (n = Z)) ->
>                 Coprime (reduceFst m n nmZ nnZ) (reduceSnd m n nmZ nnZ)
> coprimeReduce m n nmZ nnZ with (gcd (reduceFst m n nmZ nnZ) (reduceSnd m n nmZ nnZ)) proof prf
>   | Z       = void (contra p) where
>     m' : Nat
>     m' = reduceFst m n nmZ nnZ
>     n' : Nat
>     n' = reduceSnd m n nmZ nnZ
>     nm'Z : Not (m' = Z)
>     nm'Z = gcdLemma2 m n nmZ nnZ
>     nn'Z : Not (n' = Z)
>     nn'Z = gcdLemma3 m n nmZ nnZ
>     p : gcd m' n' = Z
>     p = sym prf
>     contra : Not (gcd m' n' = Z)
>     contra = gcdLemma1 m' n' nm'Z nn'Z
>   | S Z     = Refl
>   | S (S d) = void (contra d'LTEgcd) where
>     m' : Nat
>     m' = reduceFst m n nmZ nnZ
>     n' : Nat
>     n' = reduceSnd m n nmZ nnZ
>     p : gcd m' n' = S (S d)
>     p = sym prf
>     s01 : S (S d) `Divisor` m'
>     s01 = replace {x = gcd m' n'}
>                   {y = S (S d)}
>                   {P = \ ZUZU => ZUZU `Divisor` m'}
>                   p (gcdSpec1 m' n')
>     s02 : S (S d) `Divisor` n'
>     s02 = replace {x = gcd m' n'}
>                   {y = S (S d)}
>                   {P = \ ZUZU => ZUZU `Divisor` n'}
>                   p (gcdSpec2 m' n')
>     s03  : m' * (gcd m n) = m
>     s03  = gcdSpec1 m n (gcdLemma1 m n nmZ nnZ)
>     s04  : n' * (gcd m n) = n
>     s04  = gcdSpec2 m n (gcdLemma1 m n nmZ nnZ)
>     d' : Nat
>     d' = S (S d) * (gcd m n)
>     d'divm : d' `Divisor` m
>     d'divm = replace {x = m' * (gcd m n)}
>                      {y = m}
>                      {P = \ ZUZU => d' `Divisor` ZUZU}
>                      s03 (divisorLemma2 (S (S d)) m' s01 (gcd m n))
>     d'divn : d' `Divisor` n
>     d'divn = replace {x = n' * (gcd m n)}
>                      {y = n}
>                      {P = \ ZUZU => d' `Divisor` ZUZU}
>                      s04 (divisorLemma2 (S (S d)) n' s02 (gcd m n))
>     d'LTEgcd : d' `LTE` (gcd m n)
>     d'LTEgcd = gcdSpec3 m n d' d'divm d'divn nmZ nnZ
>     contra : Not (d' `LTE` (gcd m n))
>     contra = multSSNotLTE d (gcd m n) (gcdLemma1 m n nmZ nnZ)
