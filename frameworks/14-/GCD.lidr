> module GCD -- following an idea from Tim Richter

> import NatProperties

> %default total
> %hide gcd
> %hide div


Nat properties:

> plusRightInverseMinus : (m : Nat) -> (n : Nat) -> m `LTE` n -> (n - m) + m = n 

> notLTELemma : (m : Nat) -> (n : Nat) -> Not (m `LTE` n) -> n `LTE` m 


Divisor

> data Divisor : (m : Nat) -> (n : Nat) -> Type where
>   mkDivisor : (m : Nat) -> (n : Nat) -> Exists (\ q => m * q = n) -> Divisor m n

Divisor operations:

> div : (d : Nat) -> (m : Nat) -> d `Divisor` m -> Nat
> div d m (mkDivisor d m (Evidence q prf)) = q 

Divisor properties:

> anyDivisorZ : (m : Nat) -> m `Divisor` Z

> oneDivisorAny : (m : Nat) -> (S Z) `Divisor` m

> anyDivisorAny : (m : Nat) -> m `Divisor` m

> divisorPlusLemma1 : (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                      d `Divisor` m -> d `Divisor` n -> d `Divisor` (n + m)

> divisorPlusLemma2 : (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                     d `Divisor` m -> d `Divisor` n -> d `Divisor` (m + n)

> divisorMinusLemma : (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                     m `LTE` n ->
>                     d `Divisor` m -> d `Divisor` n -> d `Divisor` (n - m)

> divisorOneLemma : (d : Nat) -> (d' : Nat) -> (S d) * d' `Divisor` (S d) -> d' `Divisor` S Z

> divisorTowerLemma: (d : Nat) -> (d' : Nat) -> (m : Nat) -> 
>                    (dDm : d `Divisor` m) -> d' `Divisor` (div d m dDm) -> d * d' `Divisor` m


Greatest common divisor

> data GCD : (d : Nat) -> (m : Nat) -> (n : Nat) -> Type where
>   mkGCD : d `Divisor` m -> 
>           d `Divisor` n -> 
>           ((d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d) -> 
>           GCD d m n 

Greatest common divisor properties

> gcd : GCD d m n -> Nat
> gcd {d} (mkGCD dDm dDn dG) = d

> gcdDivisorFst : GCD d m n -> d `Divisor` m
> gcdDivisorFst {d} (mkGCD dDm dDn dG) = dDm

> gcdDivisorSnd : GCD d m n -> d `Divisor` n
> gcdDivisorSnd {d} (mkGCD dDm dDn dG) = dDn

> gcdDivisorGreatest : GCD d m n -> ((d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d) 
> gcdDivisorGreatest {d} (mkGCD dDm dDn dG) = dG

> gcdLemma : (v : GCD (S d) m n) -> 
>            d' `Divisor` (div (S d) m (gcdDivisorFst v)) -> d' `Divisor` (div (S d) n (gcdDivisorSnd v)) -> 
>            d' `Divisor` S Z
> gcdLemma {d} {d'} {m} {n} v d'DmoSd d'DnoSd = divisorOneLemma d d' Sdd'DSd where
>   SdDm    : (S d) `Divisor` m
>   SdDm    = gcdDivisorFst v
>   SdDn    : (S d) `Divisor` n
>   SdDn    = gcdDivisorSnd v
>   SdG     : (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` (S d)
>   SdG     = gcdDivisorGreatest v
>   Sdd'Dm  : (S d) * d' `Divisor` m
>   Sdd'Dm  = divisorTowerLemma (S d) d' m SdDm d'DmoSd
>   Sdd'Dn  : (S d) * d' `Divisor` n
>   Sdd'Dn  = divisorTowerLemma (S d) d' n SdDn d'DnoSd
>   Sdd'DSd : (S d) * d' `Divisor` (S d)
>   Sdd'DSd = SdG ((S d) * d') Sdd'Dm Sdd'Dn


Coprime

> data Coprime : (m : Nat) -> (n : Nat) -> Type where
>   mkCoprime : GCD d m n -> d = S Z -> Coprime m n

> gcdCoprimeLemma : (v : GCD (S d) m n) -> Coprime (div (S d) m (gcdDivisorFst v)) (div (S d) n (gcdDivisorSnd v))
> gcdCoprimeLemma {d} {m} {n} v = mkCoprime (mkGCD d'Dm' d'Dn' d'G) Refl where
>   dDm     : (S d) `Divisor` m
>   dDm     = gcdDivisorFst v
>   dDn     : (S d) `Divisor` n
>   dDn     = gcdDivisorSnd v
>   m'      : Nat
>   m'      = div (S d) m dDm
>   n'      : Nat
>   n'      = div (S d) n dDn
>   d'Dm'   : S Z `Divisor` m'
>   d'Dm'   = oneDivisorAny m'
>   d'Dn'   : S Z `Divisor` n'
>   d'Dn'   = oneDivisorAny n'
>   d'G     : (d'' : Nat) -> d'' `Divisor` m' -> d'' `Divisor` n' -> d'' `Divisor` (S Z)
>   d'G d'' = gcdLemma v


Euclid's greatest common divisor algorithm

> euclidGCD1 : GCD m m Z
> euclidGCD1 {m} = mkGCD (anyDivisorAny m) (anyDivisorZ m) (\ d' => \ d'Dm => \ d'DZ => d'Dm)

> euclidGCD2 : GCD m Z m
> euclidGCD2 {m} = mkGCD (anyDivisorZ m) (anyDivisorAny m) (\ d' => \ d'DZ => \ d'Dm => d'Dm)

> euclidGCD3 : m `LTE` n -> GCD d m (n - m) -> GCD d m n
> euclidGCD3 {m} {n} {d} p (mkGCD dDm dDnmm q) = mkGCD dDm dDn q' where
>   dDnmmpm : d `Divisor` ((n - m) + m)
>   dDnmmpm = divisorPlusLemma1 m (n - m) d dDm dDnmm
>   dDn : d `Divisor` n
>   dDn = replace {x = (n - m) + m}
>                 {y = n}
>                 {P = \ ZUZU => d `Divisor` ZUZU}
>                 (plusRightInverseMinus m n p)
>                 dDnmmpm 
>   q' : (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d
>   q' d' d'Dm d'Dn = q d' d'Dm d'Dnmm where
>     d'Dnmm : d' `Divisor` (n - m)
>     d'Dnmm = divisorMinusLemma m n d' p d'Dm d'Dn 

> euclidGCD4 : Not (m `LTE` n) -> GCD d (m - n) n -> GCD d m n
> euclidGCD4 {m} {n} {d} p (mkGCD dDmmn dDn q) = mkGCD dDm dDn q' where
>   dDmmnpn : d `Divisor` ((m - n) + n)
>   dDmmnpn = divisorPlusLemma2 (m - n) n d dDmmn dDn
>   dDm : d `Divisor` m
>   dDm = replace {x = (m - n) + n}
>                 {y = m}
>                 {P = \ ZUZU => d `Divisor` ZUZU}
>                 (plusRightInverseMinus n m (notLTELemma m n p))
>                 dDmmnpn 
>   q' : (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d
>   q' d' d'Dm d'Dn = q d' d'Dmmn d'Dn where
>     d'Dmmn : d' `Divisor` (m - n)
>     d'Dmmn = divisorMinusLemma n m d' (notLTELemma m n p) d'Dn d'Dm 

> %assert_total
> euclidGCD : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)
> euclidGCD    m   Z    = (m ** euclidGCD1)
> euclidGCD  Z       n  = (n ** euclidGCD2)
> euclidGCD (S m) (S n) with (decLTE (S m) (S n))
>   | (Yes p) = (gcd ** euclidGCD3 p P) where
>     gcdP : (d : Nat ** GCD d (S m) (S n - S m))
>     gcdP = assert_total (euclidGCD (S m) (S n - S m))
>     gcd  : Nat
>     gcd  = getWitness gcdP
>     P    : GCD gcd (S m) (S n - S m)
>     P    = getProof gcdP
>   | (No  p) = (gcd ** euclidGCD4 p P) where
>     gcdP : (d : Nat ** GCD d (S m - S n) (S n))
>     gcdP = assert_total (euclidGCD (S m - S n) (S n))
>     gcd  : Nat
>     gcd  = getWitness gcdP
>     P    : GCD gcd (S m - S n) (S n)
>     P    = getProof gcdP

> {-

> ---}
 
