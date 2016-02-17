> module Fraction


> import Syntax.PreorderReasoning


> import NatGCD
> import NatGCDOperations
> import NatGCDProperties
> import NatCoprime
> import NatCoprimeProperties
> import NatDivisor
> import NatDivisorOperations
> import NatDivisorProperties
> import NatProperties
> import Basics


> %default total


> Fraction : Type
> Fraction = (Nat, Nat)


Operations

> ||| The numerator of a fraction
> num : Fraction -> Nat
> num = fst
> -- %freeze num

> ||| The denominator of a fraction
> den : Fraction -> Nat
> den = snd
> -- %freeze den

> ||| Every natural number is a fraction
> fromNat : Nat -> Fraction
> fromNat n = (n, S Z)
> -- %freeze fromNat

> ||| Reduction to normal form (coprime numbers)
> reduce : ((m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>          Fraction -> Fraction
> reduce alg (m, n) = 
>   let dv   :  (d : Nat ** GCD d m n)
>            =  alg m n in
>   let d    :  Nat
>            =  getWitness dv in
>   let v    :  (GCD d m n)
>            =  getProof dv in 
>   let dDm  :  (d `Divisor` m)
>            =  gcdDivisorFst v in
>   let dDn  :  (d `Divisor` n)
>            =  gcdDivisorSnd v in
>   (quotient m d dDm, quotient n d dDn)
> -- %freeze reduce


> ||| Fraction addition
> plus : Fraction -> Fraction -> Fraction
> plus (n1, d1) (n2, d2) = (n1 * d2 + n2 * d1, d1 * d2)
> -- %freeze plus

> ||| Fraction multiplication
> mult : Fraction -> Fraction -> Fraction
> mult (n1, d1) (n2, d2) = (n1 * n2, d1 * d2)
> -- %freeze mult


Properties of |num|, |den|:

> ||| The denominator preserves equality
> denPreservesEquality : (x : Fraction) -> (y : Fraction) -> x = y -> den x = den y
> denPreservesEquality (n, d) (n, d) Refl = Refl


Properties of |reduce|:

> ||| Reduction of coprime numbers is identity
> reducePreservesCoprimes : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                           (x : Fraction) -> 
>                           Coprime (num x) (den x) -> 
>                           reduce alg x = x                       
> reducePreservesCoprimes alg (m, n) prf = 
>   let dv   :  (d : Nat ** GCD d m n)
>            =  alg m n in
>   let d    :  Nat
>            =  getWitness dv in
>   let v    :  (GCD d m n)
>            =  getProof dv in 
>   let dDm  :  (d `Divisor` m)
>            =  gcdDivisorFst v in
>   let dDn  :  (d `Divisor` n)
>            =  gcdDivisorSnd v in
>   let dEQ1 :  (d = S Z)
>            =  gcdOneCoprimeLemma2 m n alg prf in
>     ( reduce alg (m, n) )
>   ={ Refl }=
>     ( (quotient m d dDm, quotient n d dDn) )
>   ={ replace2 {a = Nat}
>               {a1 = quotient m d dDm}
>               {a2 = m}
>               {b = Nat}
>               {b1 = quotient n d dDn}
>               {b2 = n}
>               {P = \ ZAZA => \ ZUZU => (quotient m d dDm, quotient n d dDn) = (ZAZA, ZUZU)}
>               (quotientAnyOneAny m d dDm dEQ1) (quotientAnyOneAny n d dDn dEQ1) Refl }=
>     ( (m, n) )
>   QED
> %freeze reducePreservesCoprimes

> |||
> reducePreservesPositivity : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                             (x : Fraction) -> Z `LT` den x -> 
>                             Z `LT` den (reduce alg x)
> reducePreservesPositivity alg (m, n) zLTn =
>   let dv   :  (d : Nat ** GCD d m n)
>            =  alg m n in
>   let d    :  Nat
>            =  getWitness dv in
>   let v    :  (GCD d m n)
>            =  getProof dv in 
>   let dDn  :  (d `Divisor` n)
>            =  gcdDivisorSnd v in
>   quotientPreservesPositivity n d dDn zLTn
> %freeze reducePreservesPositivity

> ||| Reduction yields coprime numbers
> reduceYieldsCoprimes : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                        (x : Fraction) -> Z `LT` den x -> 
>                        Coprime (num (reduce alg x)) (den (reduce alg x))
> reduceYieldsCoprimes alg (m, n) zLTn =
>   let dv   :  (d : Nat ** GCD d m n)
>            =  alg m n in
>   let d    :  Nat
>            =  getWitness dv in
>   let v    :  (GCD d m n)
>            =  getProof dv in 
>   gcdCoprimeLemma'' v (gcdPreservesPositivity2 zLTn dv)
> %freeze reduceYieldsCoprimes

> ||| Reduction is idempotent (not used)
> -- reduceIdempotent : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
> --                    (x : Fraction) ->
> --                    reduce alg (reduce alg x) = reduce alg x
> -- -- %freeze reduceIdempotent


> ||| Fraction is an instance of Num
> instance Num Fraction where
>   (+) = plus
>   (*) = mult
>   fromInteger = Fraction.fromNat . fromIntegerNat


< gcdScaleInvariantCoro1 : (m : Nat) -> (n : Nat) -> (d : Nat) -> (d1 : Nat) -> (d2 : Nat) ->
<                          (dDm : d `Divisor` m) -> (dDn : d `Divisor` n) -> 
<                          GCD d1 (quotient m d dDm) (quotient n d dDn) -> GCD d2 m n -> d2 = d * d1

> ||| 
> reduceQuotientLemma : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                       (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                       (dDm : d `Divisor` m) -> (dDn : d `Divisor` n) ->
>                       reduce alg (m, n) = reduce alg (quotient m d dDm, quotient n d dDn)
> reduceQuotientLemma alg m n d dDm dDn =
>   let m'     :  Nat
>              =  quotient m d dDm in
>   let n'     :  Nat
>              =  quotient n d dDn in
>   let dv1    :  (d1 : Nat ** GCD d1 m' n')
>              =  alg m' n' in
>   let d1     :  Nat
>              =  getWitness dv1 in
>   let v1     :  (GCD d1 m' n')
>              =  getProof dv1 in 
>   let d1Dm'  :  (d1 `Divisor` m')
>              =  gcdDivisorFst v1 in
>   let d1Dn'  :  (d1 `Divisor` n')
>              =  gcdDivisorSnd v1 in
>                       
>   let dv2   :  (d2 : Nat ** GCD d2 m n)
>             =  alg m n in
>   let d2    :  Nat
>             =  getWitness dv2 in
>   let v2    :  (GCD d2 m n)
>             =  getProof dv2 in 
>   let d2Dm  :  (d2 `Divisor` m)
>             =  gcdDivisorFst v2 in
>   let d2Dn  :  (d2 `Divisor` n)
>             =  gcdDivisorSnd v2 in
>   
>   let d2EQdd1  :  (d2 = d * d1) 
>                =  gcdScaleInvariantCoro1 m n d d1 d2 dDm dDn v1 v2 in
>   let dd1Dm    :  ((d * d1) `Divisor` m)
>                =  replace {x = d2} {y = d * d1} {P = \ ZUZU => ZUZU `Divisor` m} d2EQdd1 d2Dm in
>   let dd1Dn    :  ((d * d1) `Divisor` n)
>                =  replace {x = d2} {y = d * d1} {P = \ ZUZU => ZUZU `Divisor` n} d2EQdd1 d2Dn in
>   
>     ( reduce alg (m, n) )
>   ={ Refl }=
>     ( (quotient m d2 d2Dm, quotient n d2 d2Dn) )
>   ={ ?s0 }=
>     ( (quotient m (d * d1) dd1Dm, quotient n d2 d2Dn) )
>   ={ ?s1 }=
>     ( (quotient m (d * d1) dd1Dm, quotient n (d * d1) dd1Dn) )
>   ={ ?s2 }=
>     ( (quotient m' d1 d1Dm', quotient n' d1 d1Dn') )
>   ={ Refl }=
>     ( reduce alg (quotient m d dDm, quotient n d dDn) )
>   QED


> ||| Reduction is "linear"
> reduceLinear : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                (x : Fraction) -> (y : Fraction) ->
>                reduce alg (x + y) = reduce alg (reduce alg x + reduce alg y)
> reduceLinear alg (m1, n1) (m2, n2) =
>   let dv1           :  (d1 : Nat ** GCD d1 m1 n1)
>                     =  alg m1 n1 in
>   let d1            :  Nat
>                     =  getWitness dv1 in
>   let v1            :  (GCD d1 m1 n1)
>                     =  getProof dv1 in 
>   let d1Dm1         :  (d1 `Divisor` m1)
>                     =  gcdDivisorFst v1 in
>   let d1Dn1         :  (d1 `Divisor` n1)
>                     =  gcdDivisorSnd v1 in
>   let qm1d1         :  Nat
>                     =  quotient m1 d1 d1Dm1 in
>   let qn1d1         :  Nat
>                     =  quotient n1 d1 d1Dn1 in
>                
>   let dv2           :  (d2 : Nat ** GCD d2 m2 n2)
>                     =  alg m2 n2 in
>   let d2            :  Nat
>                     =  getWitness dv2 in
>   let v2            :  (GCD d2 m2 n2)
>                     =  getProof dv2 in 
>   let d2Dm2         :  (d2 `Divisor` m2)
>                     =  gcdDivisorFst v2 in
>   let d2Dn2         :  (d2 `Divisor` n2)
>                     =  gcdDivisorSnd v2 in
>   let qm2d2         :  Nat
>                     =  quotient m2 d2 d2Dm2 in
>   let qn2d2         :  Nat
>                     =  quotient n2 d2 d2Dn2 in
>                 
>   let d2d1Dm2n1     :  ((d2 * d1) `Divisor` (m2 * n1))
>                     =  divisorMultLemma1 m2 d2 d2Dm2 n1 d1 d1Dn1 in  
>   let qm2n1d2d1     :  Nat
>                     =  quotient (m2 * n1) (d2 * d1) d2d1Dm2n1 in                
>   let d1d2Dm1n2     :  ((d1 * d2) `Divisor` (m1 * n2))
>                     =  divisorMultLemma1 m1 d1 d1Dm1 n2 d2 d2Dn2 in  
>   let qm1n2d1d2     :  Nat
>                     =  quotient (m1 * n2) (d1 * d2) d1d2Dm1n2 in
>   let d1d2Dn1n2     :  ((d1 * d2) `Divisor` (n1 * n2))
>                     =  divisorMultLemma1 n1 d1 d1Dn1 n2 d2 d2Dn2 in  
>   let qn1n2d1d2     :  Nat
>                     =  quotient (n1 * n2) (d1 * d2) d1d2Dn1n2 in
>   let d1d2Dm2n1     :  ((d1 * d2) `Divisor` (m2 * n1))
>                     =  replace {x = d2 * d1}
>                                {y = d1 * d2}
>                                {P = \ ZUZU => (ZUZU) `Divisor` (m2 * n1)}
>                                (multCommutative d2 d1) d2d1Dm2n1 in  
>   let qm2n1d1d2     :  Nat
>                     =  quotient (m2 * n1) (d1 * d2) d1d2Dm2n1 in
>   let d1d2Dm1n2m2n1 :  ((d1 * d2) `Divisor` (m1 * n2 + m2 * n1))
>                     =  divisorPlusLemma1 (m1 * n2) (m2 * n1) (d1 * d2) d1d2Dm1n2 d1d2Dm2n1 in              
>   let qm1n2m2n1d1d2 :  Nat 
>                     =  quotient (m1 * n2 + m2 * n1) (d1 * d2) d1d2Dm1n2m2n1 in
>                     
>     ( reduce alg ((m1, n1) + (m2, n2)) )
>   ={ Refl }=
>     ( reduce alg (m1 * n2 + m2 * n1, n1 * n2) )
>   ={ reduceQuotientLemma alg (m1 * n2 + m2 * n1) (n1 * n2) (d1 * d2) d1d2Dm1n2m2n1 d1d2Dn1n2 }=
>     ( reduce alg (quotient (m1 * n2 + m2 * n1) (d1 * d2) d1d2Dm1n2m2n1, 
>                   quotient (n1 * n2) (d1 * d2) d1d2Dn1n2) )
>   ={ Refl }=
>     ( reduce alg (qm1n2m2n1d1d2, qn1n2d1d2) )
>   ={ replace {x = qm1n2m2n1d1d2}
>              {y = qm1n2d1d2 + qm2n1d1d2}
>              {P = \ ZUZU => reduce alg (qm1n2m2n1d1d2, qn1n2d1d2) = reduce alg (ZUZU, qn1n2d1d2)}
>              (sym (quotientPlusLemma (m1 * n2) (m2 * n1) (d1 * d2) d1d2Dm1n2 d1d2Dm2n1))
>              Refl }=
>     ( reduce alg (qm1n2d1d2 + qm2n1d1d2, qn1n2d1d2) )
>   ={ ?s8 }=
>     ( reduce alg (qm1n2d1d2 + qm2n1d2d1, qn1n2d1d2) )
>   ={ replace {x = qn1n2d1d2}
>              {y = qn1d1 * qn2d2}
>              {P = \ ZUZU => reduce alg (qm1n2d1d2 + qm2n1d2d1, qn1n2d1d2) = reduce alg (qm1n2d1d2 + qm2n1d2d1, ZUZU)}
>              (sym (quotientMultLemma n1 d1 d1Dn1 n2 d2 d2Dn2)) Refl }=
>     ( reduce alg (qm1n2d1d2 + qm2n1d2d1, qn1d1 * qn2d2) )
>   ={ replace {x = qm2n1d2d1}
>              {y = qm2d2 * qn1d1}
>              {P = \ ZUZU => reduce alg (qm1n2d1d2 + qm2n1d2d1, qn1d1 * qn2d2) = reduce alg (qm1n2d1d2 + ZUZU, qn1d1 * qn2d2)}
>              (sym (quotientMultLemma m2 d2 d2Dm2 n1 d1 d1Dn1)) Refl }=
>     ( reduce alg (qm1n2d1d2 + qm2d2 * qn1d1, qn1d1 * qn2d2) )
>   ={ replace {x = qm1n2d1d2}
>              {y = qm1d1 * qn2d2}
>              {P = \ ZUZU => reduce alg (qm1n2d1d2 + qm2d2 * qn1d1, qn1d1 * qn2d2) = reduce alg (ZUZU + qm2d2 * qn1d1, qn1d1 * qn2d2)}
>              (sym (quotientMultLemma m1 d1 d1Dm1 n2 d2 d2Dn2)) Refl }=
>     ( reduce alg (qm1d1 * qn2d2 + qm2d2 * qn1d1, qn1d1 * qn2d2) )
>   ={ Refl }=
>     ( reduce alg ((qm1d1, qn1d1) + (qm2d2, qn2d2)) )
>   ={ Refl }=
>     ( reduce alg ((quotient m1 d1 d1Dm1, quotient n1 d1 d1Dn1) 
>                   + 
>                   (quotient m2 d2 d2Dm2, quotient n2 d2 d2Dn2)) )
>   ={ Refl }=
>     ( reduce alg (reduce alg (m1, n1) + reduce alg (m2, n2)) )
>   QED  
> %freeze reduceLinear


> ||| Addition preserves denominator positivity
> plusPreservesPositivity : (x : Fraction) -> (y : Fraction) -> 
>                           Z `LT` den x -> Z `LT` den y -> Z `LT` den (x + y)
> plusPreservesPositivity (n1, d1) (n2, d2) p q = multZeroLTZeroLT (den (n1, d1)) (den (n2, d2)) p q
> %freeze plusPreservesPositivity


> ||| Multiplication preserves denominator positivity
> multPreservesPositivity : (x : Fraction) -> (y : Fraction) -> 
>                           Z `LT` den x -> Z `LT` den y -> Z `LT` den (x * y)
> multPreservesPositivity (n1, d1) (n2, d2) p q = multZeroLTZeroLT (den (n1, d1)) (den (n2, d2)) p q
> %freeze multPreservesPositivity


> ||| Addition is commutative
> plusCommutative : (x : Fraction) -> (y : Fraction) -> x + y = y + x
> plusCommutative (n1, d1) (n2, d2) = 
>     ( (n1, d1) + (n2, d2) )
>   ={ Refl }=
>     ( (n1 * d2 + n2 * d1, d1 * d2) )
>   ={ replace {x = n1 * d2 + n2 * d1}
>              {y = n2 * d1 + n1 * d2}
>              {P = \ ZUZU => (n1 * d2 + n2 * d1, d1 * d2) = (ZUZU, d1 * d2)}
>              (Nat.plusCommutative (n1 * d2) (n2 * d1)) Refl }=
>     ( (n2 * d1 + n1 * d2, d1 * d2) )
>   ={ replace {x = d1 * d2}
>              {y = d2 * d1}
>              {P = \ ZUZU => (n2 * d1 + n1 * d2, d1 * d2) = (n2 * d1 + n1 * d2, ZUZU)}
>              (Nat.multCommutative d1 d2) Refl }=           
>     ( (n2 * d1 + n1 * d2, d2 * d1) )
>   ={ Refl }=
>     ( (n2, d2) + (n1, d1) )
>   QED
> %freeze plusCommutative


> ||| |fromInteger 0| is neutral element of addition
> plusZeroPlusRight : (x : Fraction) -> x + (fromInteger 0) = x
> plusZeroPlusRight (n, d) =
>     ( (n, d) + (fromInteger 0) )
>   ={ Refl }=
>     ( (n, d) + (Z, S Z) )
>   ={ Refl }=
>     ( (n * (S Z) + Z * d, d * (S Z)) )
>   ={ replace {x = n * (S Z)}
>              {y = n}
>              {P = \ ZUZU => (n * (S Z) + Z * d, d * (S Z)) = (ZUZU + Z * d, d * (S Z))}
>              (multOneRightNeutral n) Refl }=
>     ( (n + Z * d, d * (S Z)) )
>   ={ Refl }=
>     ( (n + Z, d * (S Z)) )
>   ={ replace {x = n + Z}
>              {y = n}
>              {P = \ ZUZU => (n + Z, d * (S Z)) = (ZUZU, d * (S Z))}
>              (plusZeroRightNeutral n) Refl }=
>     ( (n, d * (S Z)) )
>   ={ replace {x = d * (S Z)}
>              {y = d}
>              {P = \ ZUZU => (n, d * (S Z)) = (n, ZUZU)}
>              (multOneRightNeutral d) Refl }=
>     ( (n, d) )
>   QED
> %freeze plusZeroPlusRight


> ||| |fromInteger 0| is neutral element of addition
> plusZeroPlusLeft  : (x : Fraction) -> (fromInteger 0) + x = x
> plusZeroPlusLeft x = 
>     ( (fromInteger 0) + x )
>   ={ plusCommutative (fromInteger 0) x }=
>     ( x + (fromInteger 0) )
>   ={ plusZeroPlusRight x }=
>     ( x )
>   QED
> %freeze plusZeroPlusLeft


> ||| Addition is associative
> plusAssociative : (x : Fraction) -> (y : Fraction) -> (z : Fraction) -> x + (y + z) = (x + y) + z
> plusAssociative (n1, d1) (n2, d2) (n3, d3) =
>     ( (n1, d1) + ((n2, d2) + (n3, d3)) )
>   ={ Refl }=
>     ( (n1, d1) + (n2 * d3 + n3 * d2, d2 * d3) )
>   ={ Refl }=
>     ( (n1 * (d2 * d3) + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3)) )
>   ={ replace {x = n1 * (d2 * d3)}
>              {y = (n1 * d2) * d3}
>              {P = \ ZUZU => (n1 * (d2 * d3) + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3))
>                             =
>                             (ZUZU + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3))}
>              (multAssociative n1 d2 d3) Refl }=
>     ( ((n1 * d2) * d3 + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3)) )
>   ={ replace {x = (n2 * d3 + n3 * d2) * d1}
>              {y = (n2 * d3) * d1 + (n3 * d2) * d1}
>              {P = \ ZUZU => ((n1 * d2) * d3 + (n2 * d3 + n3 * d2) * d1, d1 * (d2 * d3))
>                             =
>                             ((n1 * d2) * d3 + (ZUZU), d1 * (d2 * d3))}
>              (multDistributesOverPlusLeft (n2 * d3) (n3 * d2) d1) Refl }=
>     ( ((n1 * d2) * d3 + ((n2 * d3) * d1 + (n3 * d2) * d1), d1 * (d2 * d3)) )
>   ={ replace {x = (n2 * d3) * d1}
>              {y = n2 * (d3 * d1)}
>              {P = \ ZUZU => ((n1 * d2) * d3 + ((n2 * d3) * d1 + (n3 * d2) * d1), d1 * (d2 * d3))
>                             =
>                             ((n1 * d2) * d3 + (ZUZU + (n3 * d2) * d1), d1 * (d2 * d3))}
>              (sym (multAssociative n2 d3 d1)) Refl }=
>     ( ((n1 * d2) * d3 + (n2 * (d3 * d1) + (n3 * d2) * d1), d1 * (d2 * d3)) )
>   ={ replace {x = d3 * d1}
>              {y = d1 * d3}
>              {P = \ ZUZU => ((n1 * d2) * d3 + (n2 * (d3 * d1) + (n3 * d2) * d1), d1 * (d2 * d3))
>                             =
>                             ((n1 * d2) * d3 + (n2 * (ZUZU) + (n3 * d2) * d1), d1 * (d2 * d3))}
>              (multCommutative d3 d1) Refl }=
>     ( ((n1 * d2) * d3 + (n2 * (d1 * d3) + (n3 * d2) * d1), d1 * (d2 * d3)) )
>   ={ replace {x = n2 * (d1 * d3)}
>              {y = (n2 * d1) * d3}
>              {P = \ ZUZU => ((n1 * d2) * d3 + (n2 * (d1 * d3) + (n3 * d2) * d1), d1 * (d2 * d3))
>                             =
>                             ((n1 * d2) * d3 + (ZUZU + (n3 * d2) * d1), d1 * (d2 * d3))}
>              (multAssociative n2 d1 d3) Refl }=
>     ( ((n1 * d2) * d3 + ((n2 * d1) * d3 + (n3 * d2) * d1), d1 * (d2 * d3)) )
>   ={ replace {x = (n1 * d2) * d3 + ((n2 * d1) * d3 + (n3 * d2) * d1)}
>              {y = ((n1 * d2) * d3 + (n2 * d1) * d3) + (n3 * d2) * d1}
>              {P = \ ZUZU => ((n1 * d2) * d3 + ((n2 * d1) * d3 + (n3 * d2) * d1), d1 * (d2 * d3))
>                             =
>                             (ZUZU, d1 * (d2 * d3))}
>              (plusAssociative ((n1 * d2) * d3) ((n2 * d1) * d3) ((n3 * d2) * d1)) Refl }=
>     ( (((n1 * d2) * d3 + (n2 * d1) * d3) + (n3 * d2) * d1, d1 * (d2 * d3)) )
>   ={ replace {x = (n3 * d2) * d1}
>              {y = n3 * (d2 * d1)}
>              {P = \ ZUZU => (((n1 * d2) * d3 + (n2 * d1) * d3) + (n3 * d2) * d1, d1 * (d2 * d3))
>                             =
>                             (((n1 * d2) * d3 + (n2 * d1) * d3) + ZUZU, d1 * (d2 * d3))}
>              (sym (multAssociative n3 d2 d1)) Refl }=         
>     ( (((n1 * d2) * d3 + (n2 * d1) * d3) + n3 * (d2 * d1), d1 * (d2 * d3)) )
>   ={ replace {x = (n1 * d2) * d3 + (n2 * d1) * d3}
>              {y = (n1 * d2 + n2 * d1) * d3}
>              {P = \ ZUZU => (((n1 * d2) * d3 + (n2 * d1) * d3) + n3 * (d2 * d1), d1 * (d2 * d3))
>                             =
>                             (ZUZU + n3 * (d2 * d1), d1 * (d2 * d3))}
>              (sym (multDistributesOverPlusLeft (n1 * d2) (n2 * d1) d3)) Refl }=
>     ( ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), d1 * (d2 * d3)) )
>   ={ replace {x = d1 * (d2 * d3)}
>              {y = (d1 * d2) * d3}
>              {P = \ ZUZU => ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), d1 * (d2 * d3))
>                             =
>                             ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), ZUZU)}
>              (multAssociative d1 d2 d3) Refl }=  
>     ( ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), (d1 * d2) * d3) )
>   ={ replace {x = d2 * d1}
>              {y = d1 * d2}
>              {P = \ ZUZU => ((n1 * d2 + n2 * d1) * d3 + n3 * (d2 * d1), (d1 * d2) * d3)
>                             =
>                             ((n1 * d2 + n2 * d1) * d3 + n3 * (ZUZU), (d1 * d2) * d3)}
>              (multCommutative d2 d1) Refl }=
>     ( ((n1 * d2 + n2 * d1) * d3 + n3 * (d1 * d2), (d1 * d2) * d3) )
>   ={ Refl }=
>     ( (n1 * d2 + n2 * d1, d1 * d2) + (n3, d3) )
>   ={ Refl }=
>     ( ((n1, d1) + (n2, d2)) + (n3, d3) )
>   QED
> %freeze plusAssociative


> ||| Multiplication is commutative
> multCommutative : (x : Fraction) -> (y : Fraction) -> x * y = y * x
> multCommutative (n1, d1) (n2, d2) = 
>     ( (n1, d1) * (n2, d2) )
>   ={ Refl }=
>     ( (n1 * n2, d1 * d2) )
>   ={ replace {x = n1 * n2}
>              {y = n2 * n1}
>              {P = \ ZUZU => (n1 * n2, d1 * d2) = (ZUZU, d1 * d2)}
>              (Nat.multCommutative n1 n2) Refl }=
>     ( (n2 * n1, d1 * d2) )
>   ={ replace {x = d1 * d2}
>              {y = d2 * d1}
>              {P = \ ZUZU => (n2 * n1, d1 * d2) = (n2 * n1, ZUZU)}
>              (Nat.multCommutative d1 d2) Refl }=           
>     ( (n2 * n1, d2 * d1) )
>   ={ Refl }=
>     ( (n2, d2) * (n1, d1) )
>   QED
> %freeze multCommutative


> |||
> multOneRight : (x : Fraction) -> x * (fromInteger 1) = x
> multOneRight (n, d) = 
>     ( (n, d) * (S Z, S Z) )
>   ={ Refl }=
>     ( (n * (S Z), d * (S Z)) )
>   ={ replace {x = n * (S Z)}
>              {y = n}
>              {P = \ ZUZU => (n * (S Z), d * (S Z)) = (ZUZU, d * (S Z))}
>              (multOneRightNeutral n) Refl }=
>     ( (n, d * (S Z)) )
>   ={ replace {x = d * (S Z)}
>              {y = d}
>              {P = \ ZUZU => (n, d * (S Z)) = (n, ZUZU)}
>              (multOneRightNeutral d) Refl }=           
>     ( (n, d) )
>   QED
> %freeze multOneRight


> |||
> multOneLeft : (x : Fraction) -> (fromInteger 1) * x = x
> multOneLeft x = 
>     ( (fromInteger 1) * x )
>   ={ multCommutative (fromInteger 1) x }=
>     ( x * (fromInteger 1) )
>   ={ multOneRight x }=
>     ( x )
>   QED
> %freeze multOneLeft

> {-

> ---}
