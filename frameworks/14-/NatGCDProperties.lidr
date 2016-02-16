> module NatGCDProperties


> import NatGCD
> import NatGCDOperations
> import NatDivisor
> import NatDivisorOperations
> import NatDivisorProperties
> import NatProperties
> import Basics
> import Sigma
> import PairsOperations


> %default total

> %access public export


> ||| 
> gcdUnique : (d1 : Nat) -> (d2 : Nat) -> GCD d1 m n -> GCD d2 m n -> d1 = d2
> gcdUnique d1 d2 (MkGCD d1Dm d1Dn d1G) (MkGCD d2Dm d2Dn d2G) = s3 where
>   s1 : d1 `Divisor` d2
>   s1 = d2G d1 d1Dm d1Dn
>   s2 : d2 `Divisor` d1
>   s2 = d1G d2 d2Dm d2Dn
>   s3 : d1 = d2
>   s3 = divisorAntisymmetric d1 d2 s1 s2
> %freeze gcdUnique


> ||| 
> gcdCommutative : GCD d m n -> GCD d n m
> gcdCommutative (MkGCD dDm dDn dG) = (MkGCD dDn dDm (\ d' => \ n => \ m => dG d' m n))
> %freeze gcdCommutative


> ||| If |m| is positive, the greatest common divisor of |m| and |n| is positive
> gcdPreservesPositivity1 : Z `LT` m -> (dv : Sigma Nat (\ d => GCD d m n)) -> Z `LT` (getWitness dv)
> gcdPreservesPositivity1 {m} zLTm (MkSigma d prf) = multLTZeroLeftLTZero d q zLTdq where
>   dDm : d `Divisor` m
>   dDm = gcdDivisorFst prf
>   q : Nat
>   q = quotient m d dDm
>   zLTdq : Z `LT` (d * q)
>   zLTdq = replace {x = m} 
>                   {y = d * q} 
>                   {P = \ ZUZU => Z `LT` ZUZU}  
>                   (sym (quotientLemma m d dDm)) zLTm 
> %freeze gcdPreservesPositivity1

> ||| If |n| is positive, the greatest common divisor of |m| and |n| is positive
> gcdPreservesPositivity2 : Z `LT` n -> (dv : Sigma Nat (\ d => GCD d m n)) -> Z `LT` (getWitness dv)
> gcdPreservesPositivity2 {n} zLTn (MkSigma d prf) = multLTZeroLeftLTZero d q zLTdq where
>   dDn : d `Divisor` n
>   dDn = gcdDivisorSnd prf
>   q : Nat
>   q = quotient n d dDn
>   zLTdq : Z `LT` (d * q)
>   zLTdq = replace {x = n} 
>                   {y = d * q} 
>                   {P = \ ZUZU => Z `LT` ZUZU}  
>                   (sym (quotientLemma n d dDn)) zLTn 
> %freeze gcdPreservesPositivity2

> ||| 
> gcdLemma : (v : GCD (S d) m n) ->
>            d' `Divisor` (quotient m (S d) (gcdDivisorFst v)) ->
>            d' `Divisor` (quotient n (S d) (gcdDivisorSnd v)) ->
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
> %freeze gcdLemma

> |||
> gcdLemma' : (v : GCD d m n) -> Not (d = Z) ->
>             d' `Divisor` (quotient m d (gcdDivisorFst v)) ->
>             d' `Divisor` (quotient n d (gcdDivisorSnd v)) ->
>             d' `Divisor` S Z
> gcdLemma' {d} {d'} {m} {n} v dNotZ d'DmoSd d'DnoSd = divisorOneLemma' d d' dNotZ Sdd'DSd where
>   SdDm    : d `Divisor` m
>   SdDm    = gcdDivisorFst v
>   SdDn    : d `Divisor` n
>   SdDn    = gcdDivisorSnd v
>   SdG     : (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d
>   SdG     = gcdDivisorGreatest v
>   Sdd'Dm  : d * d' `Divisor` m
>   Sdd'Dm  = divisorTowerLemma d d' m SdDm d'DmoSd
>   Sdd'Dn  : d * d' `Divisor` n
>   Sdd'Dn  = divisorTowerLemma d d' n SdDn d'DnoSd
>   Sdd'DSd : d * d' `Divisor` d
>   Sdd'DSd = SdG (d * d') Sdd'Dm Sdd'Dn
> %freeze gcdLemma'

> |||
> gcdLemma'' : (d : Nat) -> (m : Nat) -> (n : Nat) -> 
>              (dDm : d `Divisor` m) -> (dDn : d `Divisor` n) -> 
>              (v : GCD d m n) -> Z `LT` d ->
>              (d' : Nat) ->
>              d' `Divisor` (quotient m d dDm) ->
>              d' `Divisor` (quotient n d dDn) ->
>              d' `Divisor` S Z
> gcdLemma'' d m n dDm dDn v zLTd d' d'Dqmd d'Dqnd = divisorOneLemma'' d d' zLTd dd'Dd where
>   dG     : (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` d
>   dG     = gcdDivisorGreatest v
>   dd'Dm  : d * d' `Divisor` m
>   dd'Dm  = divisorTowerLemma d d' m dDm d'Dqmd
>   dd'Dn  : d * d' `Divisor` n
>   dd'Dn  = divisorTowerLemma d d' n dDn d'Dqnd
>   dd'Dd  : d * d' `Divisor` d
>   dd'Dd  = dG (d * d') dd'Dm dd'Dn
> %freeze gcdLemma''


> ||| d GCD ((S a) * m) ((S a) * n) => d/(S a) GCD m n
> ||| 
> ||| The implementation is based on a proof by Tim Richter. We have to show
> |||
> |||   1) d/(S a) is a divisor of m
> |||   2) d/(S a) is a divisor of n
> |||   3) if d' is a divisor of m and n, then d' is a divisor of d/(S a)
> ||| 
> ||| We know from |quotientDivisorLemma| that
> |||   
> |||   a|b, b|c, a|c => (b/a)|(c/a)
> |||
> ||| Thus, we can prove 1) and 2) by applying the lemma to
> |||
> |||   (S a)|d, d|((S a) * m), (S a)|((S a) * m)
> |||
> |||   and
> |||
> |||   (S a)|d, d|((S a) * n), (S a)|((S a) * n)
> |||
> ||| and using |quotientCancellationLemma| to reduce ((S a) * m)/(S a) and
> ||| ((S a) * n)/(S a) to m and n, respectively. Since d is the GCD of 
> ||| (S a) * m and (S a) * n and (S a) is trivially a divisor of both, we
> ||| readily have (S a)|d. d|((S a) * m) and d|((S a) * m) also diretly follow
> ||| from d being the GCD of (S a) * m and (S a) * n. 
> |||
> ||| In order to prove 3), we again apply |quotientDivisorLemma|, this time to
> ||| 
> |||   (S a)|((S a) * d'), ((S a) * d')|d, (S a)|d
> |||
> ||| We derive ((S a) * d')|d from the hypothesis d'|m, d'|n by pre-multiplying
> ||| by (S a) (and using |divisorMultLemma1|). This yields
> |||
> |||   ((S a) * d')|((S a) * m), ((S a) * d')|((S a) * n)
> |||
> ||| The result directly follows from d being the GCD of (S a) * m and (S a) * n.
> |||
> gcdDivisorLemma : (d : Nat) -> (m : Nat) -> (n : Nat) -> (a : Nat) ->
>                   GCD d ((S a) * m) ((S a) * n) -> 
>                   Sigma ((S a) `Divisor` d) (\ saDd => GCD (quotient d (S a) saDd) m n)

> gcdDivisorLemma d m n a v = MkSigma saDd (MkGCD qDm qDn qG) where
>   dDsam   :  d `Divisor` ((S a) * m)
>   dDsam   =  gcdDivisorFst v
>   saDsam  :  S a `Divisor` ((S a) * m)
>   saDsam  =  Element m Refl
>   dDsan   :  d `Divisor` ((S a) * n)
>   dDsan   =  gcdDivisorSnd v
>   saDsan  :  S a `Divisor` ((S a) * n)
>   saDsan  =  Element n Refl
>   saDd    :  (S a) `Divisor` d
>   saDd    =  gcdDivisorGreatest {d = d} v (S a) saDsam saDsan

>   q       :  Nat
>   q       =  quotient d (S a) saDd
>   preqDm  :  q `Divisor` (quotient ((S a) * m) (S a) saDsam)
>   preqDm  =  quotientDivisorLemma a d ((S a) * m) saDd dDsam saDsam
>   qDm     :  q `Divisor` m
>   qDm     =  replace {x = quotient ((S a) * m) (S a) saDsam}
>                      {y = m}
>                      {P = \ ZUZU => q `Divisor` ZUZU}
>                      (quotientCancellationLemma m a saDsam) preqDm
    
>   preqDn  :  q `Divisor` (quotient ((S a) * n) (S a) saDsan)
>   preqDn  =  quotientDivisorLemma a d ((S a) * n) saDd dDsan saDsan
>   qDn     :  q `Divisor` n
>   qDn     =  replace {x = quotient ((S a) * n) (S a) saDsan}
>                      {y = n}
>                      {P = \ ZUZU => q `Divisor` ZUZU}
>                      (quotientCancellationLemma n a saDsan) preqDn
   
>   preqG   :  (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> 
>              (quotient ((S a) * d') (S a) (Element d' Refl)) `Divisor` q
>   preqG d' d'Dm d'Dn  =  quotientDivisorLemma a ((S a) * d') d (Element d' Refl) sad'Dd saDd
>     where sad'Dsam  :  ((S a) * d') `Divisor` ((S a) * m)
>           sad'Dsam  =  divisorMultLemma1 (S a) (S a) (anyDivisorAny (S a)) m d' d'Dm
>           sad'Dsan  :  ((S a) * d') `Divisor` ((S a) * n)
>           sad'Dsan  =  divisorMultLemma1 (S a) (S a) (anyDivisorAny (S a)) n d' d'Dn
>           sad'Dd    :  ((S a) * d') `Divisor` d
>           sad'Dd    =  gcdDivisorGreatest {d = d} v ((S a) * d') sad'Dsam sad'Dsan
>
>   qG      :  (d' : Nat) -> d' `Divisor` m -> d' `Divisor` n -> d' `Divisor` q
>   qG    d' d'Dm d'Dn     =  replace {x = quotient ((S a) * d') (S a) (Element d' Refl)}
>                                     {y = d'}
>                                     {P = \ ZUZU => ZUZU `Divisor` q}
>                                     (quotientCancellationLemma d' a (Element d' Refl)) (preqG d' d'Dm d'Dn)
> %freeze gcdDivisorLemma

> |||
> gcdScaleInvariant : (d : Nat) -> (m : Nat) -> (n : Nat) -> (d' : Nat) -> (a : Nat) ->
>                     GCD d m n -> GCD d' (a * m) (a * n) -> d' = a * d
> gcdScaleInvariant d m n d'  Z    v  v' = s6 where
>   s0   :  Z `Divisor` (Z * m)
>   s0   =  Element m Refl
>   s1   :  Z `Divisor` (Z * n)
>   s1   =  Element n Refl
>   s2   :  Z `Divisor` d'
>   s2   =  gcdDivisorGreatest {d = d'} v' Z s0 s1
>   s3   :  Nat
>   s3   =  getWitness s2
>   s4   :  Z * s3 = d'
>   s4   =  getProof s2
>   s5   :  d' = Z
>   s5   =  replace {x = Z * s3} {y = Z} {P = \ ZUZU => d' = ZUZU} (multZeroLeftZero s3) (sym s4)
>   s6   :  d' = Z * d
>   s6   =  replace {x = Z} {y = Z * d} {P = \ ZUZU => d' = ZUZU} (sym (multZeroLeftZero d)) s5
> gcdScaleInvariant d m n d' (S a) v  v' = s4 where
>   s0   :  (S a) `Divisor` d'
>   s0   =  getWitness (gcdDivisorLemma d' m n a v')
>   s1   :  GCD (quotient d' (S a) s0) m n 
>   s1   =  getProof (gcdDivisorLemma d' m n a v')
>   s2   :  quotient d' (S a) s0 = d
>   s2   =  gcdUnique (quotient d' (S a) s0) d s1 v
>   s3   :  (S a) * (quotient d' (S a) s0) = (S a) * d
>   s3   =  multPreservesEq (S a) (S a) (quotient d' (S a) s0) d Refl s2
>   s4   :  d' = (S a) * d
>   s4   =  replace {x = (S a) * (quotient d' (S a) s0)}
>                   {y = d'}
>                   {P = \ ZUZU => ZUZU = (S a) * d}
>                   (quotientLemma d' (S a) s0) s3
> %freeze gcdScaleInvariant

> |||
> gcdScaleInvariantCoro1 : (m : Nat) -> (n : Nat) -> (d : Nat) -> (d1 : Nat) -> (d2 : Nat) ->
>                          (dDm : d `Divisor` m) -> (dDn : d `Divisor` n) -> 
>                          GCD d1 (quotient m d dDm) (quotient n d dDn) -> GCD d2 m n -> d2 = d * d1
> gcdScaleInvariantCoro1 m n d d1 d2 dDm dDn v1 v2 =
>   gcdScaleInvariant d1 (quotient m d dDm) (quotient n d dDn) d2 d v1 v2' where
>     v2'  :  GCD d2 (d * (quotient m d dDm)) (d * (quotient n d dDn))
>     v2'  =  replace2 {a = Nat} {a1 = m} {a2 = d * (quotient m d dDm)} 
>                      {b = Nat} {b1 = n} {b2 = d * (quotient n d dDn)} 
>                      {P = \ ZAZA => \ ZUZU => GCD d2 ZAZA ZUZU}
>                      (sym (quotientLemma m d dDm)) (sym (quotientLemma n d dDn)) v2
> %freeze gcdScaleInvariantCoro1

