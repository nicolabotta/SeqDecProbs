> module NatCoprimeProperties


> import NatCoprime
> import NatGCD
> import NatGCDOperations
> import NatGCDProperties
> import NatDivisor
> import NatDivisorOperations
> import NatDivisorProperties
> import NatProperties


> %default total


> ||| Coprime is decidable
> decCoprime : ((a : Nat) -> (b : Nat) -> (d : Nat ** GCD d a b)) ->
>              (m : Nat) -> (n : Nat) ->
>              Dec (Coprime m n)
> decCoprime alg m n with (alg m n)
>   | (d ** v) with (decEq d (S Z))
>     | (Yes p) = Yes (MkCoprime {d = d} v p)
>     | (No contra) = No contra' where
>         contra' : Coprime m n -> Void
>         contra' (MkCoprime {d = d'} v' p') = contra p where
>           p : d = S Z
>           p = replace {x = d'}
>                       {y = d}
>                       {P = \ ZUZU => ZUZU = S Z}
>                       (gcdUnique d' d v' v) p'
> %freeze decCoprime

> ||| Coprime is symmetric
> symmetricCoprime : Coprime m n -> Coprime n m
> symmetricCoprime {m} {n} (MkCoprime (MkGCD {d} {m} {n} dDm dDn dG)  dEQone) =
>                          (MkCoprime (MkGCD             dDn dDm dG') dEQone) where
>     dG' : (d' : Nat) -> Divisor d' n -> Divisor d' m -> Divisor d' d
>     dG' d' d'Dn d'Dm = dG d' d'Dm d'Dn
> %freeze symmetricCoprime

> ||| Any number is coprime with one
> anyCoprimeOne : Coprime m (S Z)
> anyCoprimeOne {m} = MkCoprime (MkGCD oDm oDo oG) Refl where
>   oDm : (S Z) `Divisor` m
>   oDm = oneDivisorAny m
>   oDo : (S Z) `Divisor` (S Z)
>   oDo = anyDivisorAny (S Z)
>   oG  : (d : Nat) -> d `Divisor` m -> d `Divisor` (S Z) -> d `Divisor` (S Z)
>   oG d dDm dDo = dDo
> %freeze anyCoprimeOne

> ||| Division by gcd yields coprime numbers
> gcdCoprimeLemma : (v : GCD (S d) m n) -> Coprime (quotient m (S d) (gcdDivisorFst v))
>                                                  (quotient n (S d) (gcdDivisorSnd v))
> gcdCoprimeLemma {d} {m} {n} v = MkCoprime (MkGCD d'Dm' d'Dn' d'G) Refl where
>   dDm     : (S d) `Divisor` m
>   dDm     = gcdDivisorFst v
>   dDn     : (S d) `Divisor` n
>   dDn     = gcdDivisorSnd v
>   m'      : Nat
>   m'      = quotient m (S d) dDm
>   n'      : Nat
>   n'      = quotient n (S d) dDn
>   d'Dm'   : S Z `Divisor` m'
>   d'Dm'   = oneDivisorAny m'
>   d'Dn'   : S Z `Divisor` n'
>   d'Dn'   = oneDivisorAny n'
>   d'G     : (d'' : Nat) -> d'' `Divisor` m' -> d'' `Divisor` n' -> d'' `Divisor` (S Z)
>   d'G d'' = gcdLemma v
> %freeze gcdCoprimeLemma

> ||| Division by gcd yields coprime numbers
> gcdCoprimeLemma' : (v : GCD d m n) -> Not (d = Z) -> Coprime (quotient m d (gcdDivisorFst v))
>                                                              (quotient n d (gcdDivisorSnd v))
> gcdCoprimeLemma' {d} {m} {n} v dNotZ = MkCoprime (MkGCD d'Dm' d'Dn' d'G) Refl where
>   dDm     : d `Divisor` m
>   dDm     = gcdDivisorFst v
>   dDn     : d `Divisor` n
>   dDn     = gcdDivisorSnd v
>   m'      : Nat
>   m'      = quotient m d dDm
>   n'      : Nat
>   n'      = quotient n d dDn
>   d'Dm'   : S Z `Divisor` m'
>   d'Dm'   = oneDivisorAny m'
>   d'Dn'   : S Z `Divisor` n'
>   d'Dn'   = oneDivisorAny n'
>   d'G     : (d'' : Nat) -> d'' `Divisor` m' -> d'' `Divisor` n' -> d'' `Divisor` (S Z)
>   d'G d'' = gcdLemma' v dNotZ
> %freeze gcdCoprimeLemma'

> ||| Division by gcd yields coprime numbers
> gcdCoprimeLemma'' : (v : GCD d m n) -> Z `LT` d -> Coprime (quotient m d (gcdDivisorFst v))
>                                                            (quotient n d (gcdDivisorSnd v))
> gcdCoprimeLemma'' {d} {m} {n} v zLTd = MkCoprime (MkGCD d'Dm' d'Dn' d'G) Refl where
>   dDm     : d `Divisor` m
>   dDm     = gcdDivisorFst v
>   dDn     : d `Divisor` n
>   dDn     = gcdDivisorSnd v
>   m'      : Nat
>   m'      = quotient m d dDm
>   n'      : Nat
>   n'      = quotient n d dDn
>   d'Dm'   : S Z `Divisor` m'
>   d'Dm'   = oneDivisorAny m'
>   d'Dn'   : S Z `Divisor` n'
>   d'Dn'   = oneDivisorAny n'
>   dNotZ   : Not (d = Z)
>   dNotZ   = gtZisnotZ zLTd
>   d'G     : (d'' : Nat) -> d'' `Divisor` m' -> d'' `Divisor` n' -> d'' `Divisor` (S Z)
>   d'G d'' = gcdLemma' v dNotZ
> %freeze gcdCoprimeLemma''


GCD / Coprime properties:

> |||
> gcdOneCoprimeLemma1 : (alg : (a : Nat) -> (b : Nat) -> (d : Nat ** GCD d a b)) ->
>                       (m : Nat) -> (n : Nat) ->
>                       gcd (alg m n) = S Z -> Coprime m n
> gcdOneCoprimeLemma1 alg m n prf = MkCoprime (getProof (alg m n)) prf
> %freeze gcdOneCoprimeLemma1

> |||
> gcdOneCoprimeLemma2 : (m : Nat) -> (n : Nat) ->
>                       (alg : (a : Nat) -> (b : Nat) -> (d : Nat ** GCD d a b)) ->
>                       Coprime m n -> gcd (alg m n) = S Z
> gcdOneCoprimeLemma2 m n alg (MkCoprime {d} v prf) = s3 where
>   s1 : d = S Z
>   s1 = prf
>   s2 : gcd (alg m n) = d
>   s2 = gcdUnique (gcd (alg m n)) d (getProof (alg m n)) v
>   s3 : gcd (alg m n) = S Z
>   s3 = trans s2 s1
> %freeze gcdOneCoprimeLemma2

> |||
> gcdAnyOneOne : (alg : (a : Nat) -> (b : Nat) -> (d : Nat ** GCD d a b)) ->
>                (m : Nat) ->
>                gcd (alg m (S Z)) = S Z
> gcdAnyOneOne alg m = gcdOneCoprimeLemma2 m (S Z) alg anyCoprimeOne
> %freeze gcdAnyOneOne
