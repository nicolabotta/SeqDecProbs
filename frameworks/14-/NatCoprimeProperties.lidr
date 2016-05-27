> module NatCoprimeProperties


> import NatCoprime
> import NatGCD
> import NatGCDOperations
> import NatGCDProperties
> import NatDivisor
> import NatDivisorOperations
> import NatDivisorProperties
> import NatOperationsProperties
> import NatGCDAlgorithm
> import NatGCDEuclid
> import PairsOperations
> import Sigma


> %default total
> %access public export
> %auto_implicits on


> ||| Coprime is decidable
> decCoprime : (m : Nat) -> (n : Nat) -> Dec (Coprime m n)
> decCoprime m n with (decEq (gcdAlg m n) (S Z))
>   | (Yes p) = Yes (MkCoprime p)
>   | (No contra) = No contra' where
>         contra' : Coprime m n -> Void
>         contra' (MkCoprime p) = contra p
> %freeze decCoprime


> ||| Coprime is symmetric
> symmetricCoprime : Coprime m n -> Coprime n m
> symmetricCoprime {m} {n} (MkCoprime prf) = MkCoprime (trans (gcdAlgCommutative n m) prf)
> %freeze symmetricCoprime


> ||| Any number is coprime with one
> anyCoprimeOne : Coprime m (S Z)
> anyCoprimeOne {m} = MkCoprime s3 where
>   s1 : (gcdAlg m (S Z)) `Divisor` (S Z)
>   s1 = gcdDivisorSnd (gcdAlgLemma m (S Z))
>   s2 : (S Z ) `Divisor` (gcdAlg m (S Z))
>   s2 = oneDivisorAny (gcdAlg m (S Z))
>   s3 : gcdAlg m (S Z) = S Z
>   s3 = divisorAntisymmetric (gcdAlg m (S Z)) (S Z) s1 s2
> %freeze anyCoprimeOne


> ||| Division by gcd yields coprime numbers
> gcdCoprimeLemma : (d : Nat) -> (m : Nat) -> (n : Nat) -> 
>                   (dDm : d `Divisor` m) -> (dDn : d `Divisor` n) -> 
>                   Z `LT` d -> GCD d m n -> Coprime (quotient m d dDm) (quotient n d dDn)
> gcdCoprimeLemma d m n dDm dDn zLTd dGCDmn =
>   let m'         :  Nat
>                  =  quotient m d dDm in
>   let n'         :  Nat
>                  =  quotient n d dDn in
>   let d'         :  Nat
>                  =  gcdAlg m' n' in
>   let d'GCDm'n'  :  (GCD d' m' n')
>                  =  gcdAlgLemma m' n' in
>   let d'Dm'      :  (d' `Divisor` m')
>                  =  gcdDivisorFst d'GCDm'n' in
>   let d'Dn'      :  (d' `Divisor` n')
>                  =  gcdDivisorSnd d'GCDm'n' in
>   let oneDd'     :  ((S Z) `Divisor` d')
>                  =  oneDivisorAny d' in
>   let d'Done     :  (d' `Divisor` (S Z))
>                  =  gcdLemma'' d m n dDm dDn dGCDmn zLTd d' d'Dm' d'Dn' in
>   let d'EQone    :  (d' = (S Z)) 
>                  =  divisorAntisymmetric d' (S Z) d'Done oneDd' in
>   MkCoprime d'EQone




> {-

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

> ---}
