> module FractionProperties

> import Syntax.PreorderReasoning

> import Fraction
> import FractionOperations
> import PNat
> import PNatOperations
> import PNatProperties
> import Basics
> import NatProperties
> import NatGCD
> import NatGCDOperations
> import NatGCDProperties
> import NatDivisor
> import NatDivisorOperations
> import NatDivisorProperties
> import NatCoprime
> import NatCoprimeProperties
> import NatGCDAlgorithm
> import NatGCDEuclid


> %default total


-- > ||| Fraction is an instance of Show
-- > instance Show Fraction where
-- >   show x = show (num x) ++ "/" ++ show (den x)


> ||| Fraction is an instance of Num
> instance Num Fraction where
>   (+) = plus
>   (*) = mult
>   fromInteger = fromNat . fromIntegerNat


> ||| Addition is commutative
> plusCommutative : (x : Fraction) -> (y : Fraction) -> x + y = y + x
> plusCommutative (m, d') (n, e') =
>   let d = toNat d' in
>   let e = toNat e' in
>     ( (m, d') + (n, e') )
>   ={ Refl }=
>     ( (m * e + n * d, d' * e') )
>   ={ cong2 (plusCommutative (m * e) (n * d)) (multCommutative d' e') }=
>     ( (n * d + m * e, e' * d') )
>   ={ Refl }=
>     ( (n, e') + (m, d') )
>   QED
> %freeze plusCommutative


> ||| |fromInteger 0| is neutral element of addition
> plusZeroRightNeutral : (x : Fraction) -> x + (fromInteger 0) = x
> plusZeroRightNeutral (n, d') =
>   let d = toNat d' in
>     ( (n, d') + (fromInteger 0) )
>   ={ Refl }=
>     ( (n, d') + fromNat (fromIntegerNat 0) )
>   ={ Refl }=
>     ( (n, d') + fromNat 0 )
>   ={ Refl }=
>     ( (n, d') + (0, Element 1 MkIsSucc) )
>   ={ Refl }=
>     ( (n * 1 + 0 * d, d' * (Element 1 MkIsSucc)) )
>   ={ cong2 (multOneRightNeutralPlusMultZeroLeftZero n d) (multOneRightNeutral d') }=
>     ( (n, d') )
>   QED
> %freeze plusZeroRightNeutral


> ||| |fromInteger 0| is neutral element of addition
> plusZeroLeftNeutral  : (x : Fraction) -> (fromInteger 0) + x = x
> plusZeroLeftNeutral x = 
>     ( (fromInteger 0) + x )
>   ={ plusCommutative (fromInteger 0) x }=
>     ( x + (fromInteger 0) )
>   ={ plusZeroRightNeutral x }=
>     ( x )
>   QED
> %freeze plusZeroLeftNeutral


> ||| Multiplication is commutative
> multCommutative : (x : Fraction) -> (y : Fraction) -> x * y = y * x
> multCommutative (m, d') (n, e') =
>     ( (m, d') * (n, e') )
>   ={ Refl }=
>     ( (m * n, d' * e') )
>   ={ cong2 (multCommutative m n) (multCommutative d' e') }=
>     ( (n * m, e' * d') )
>   ={ Refl }=
>     ( (n, e') * (m, d') )
>   QED
> %freeze multCommutative


> ||| |fromInteger 1| is neutral element of multiplication
> multOneRightNeutral : (x : Fraction) -> x * (fromInteger 1) = x
> multOneRightNeutral (n, d') =
>   let d = toNat d' in
>     ( (n, d') * (fromInteger 1) )
>   ={ Refl }=
>     ( (n, d') * (fromNat (fromIntegerNat 1)) )
>   ={ Refl }=
>     ( (n, d') * (fromNat 1) )
>   ={ Refl }=
>     ( (n, d') * (1, Element 1 MkIsSucc) )
>   ={ Refl }=
>     ( (n * 1, d' * (Element 1 MkIsSucc)) )
>   ={ cong2 (multOneRightNeutral n) (multOneRightNeutral d') }=
>     ( (n, d') )
>   QED
> %freeze multOneRightNeutral


> ||| |fromInteger 1| is neutral element of multiplication
> multOneLeftNeutral  : (x : Fraction) -> (fromInteger 1) * x = x
> multOneLeftNeutral x = 
>     ( (fromInteger 1) * x )
>   ={ multCommutative (fromInteger 1) x }=
>     ( x * (fromInteger 1) )
>   ={ multOneRightNeutral x }=
>     ( x )
>   QED
> %freeze multOneLeftNeutral


> ||| Addition is associative
> plusAssociative : (x : Fraction) -> (y : Fraction) -> (z : Fraction) -> x + (y + z) = (x + y) + z
> plusAssociative (m, d') (n, e') (o, f') = 
>   let d = toNat d' in
>   let e = toNat e' in
>   let f = toNat f' in
>     ( (m, d') + ((n, e') + (o, f')) )
>   ={ Refl }=
>     ( (m, d') + (n * f + o * e, e' * f') )
>   ={ Refl }=
>     ( (m * (toNat (e' * f')) + (n * f + o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (m * (ZUZU) + (n * f + o * e) * d, d' * (e' * f'))} 
>           toNatMultLemma }=
>     ( (m * (e * f) + (n * f + o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (m * (e * f) + ZUZU, d' * (e' * f'))} 
>           (multDistributesOverPlusLeft (n * f) (o * e) d) }=
>     ( (m * (e * f) + ((n * f) * d + (o * e) * d), d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (ZUZU, d' * (e' * f'))}
>           (plusAssociative (m * (e * f)) ((n * f) * d) ((o * e) * d)) }=
>     ( ((m * (e * f) + (n * f) * d) + (o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => ((ZUZU + (n * f) * d) + (o * e) * d, d' * (e' * f'))}
>           (multAssociative m e f) }=
>     ( (((m * e) * f + (n * f) * d) + (o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (((m * e) * f + ZUZU) + (o * e) * d, d' * (e' * f'))}
>           (sym (multAssociative n f d)) }=
>     ( (((m * e) * f + n * (f * d)) + (o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (((m * e) * f + n * (ZUZU)) + (o * e) * d, d' * (e' * f'))}
>           (multCommutative f d) }=
>     ( (((m * e) * f + n * (d * f)) + (o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (((m * e) * f + ZUZU) + (o * e) * d, d' * (e' * f'))}
>           (multAssociative n d f) }=
>     ( (((m * e) * f + (n * d) * f) + (o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => (ZUZU + (o * e) * d, d' * (e' * f'))}
>           (sym (multDistributesOverPlusLeft (m * e) (n * d) f)) }=
>     ( ((m * e + n * d) * f + (o * e) * d, d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => ((m * e + n * d) * f + ZUZU, d' * (e' * f'))}
>           (sym (multAssociative o e d)) }=
>     ( ((m * e + n * d) * f + o * (e * d), d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => ((m * e + n * d) * f + o * (ZUZU), d' * (e' * f'))}
>           (multCommutative e d) }=  
>     ( ((m * e + n * d) * f + o * (d * e), d' * (e' * f')) )
>   ={ cong {f = \ ZUZU => ((m * e + n * d) * f + o * (d * e), ZUZU)}
>           (multAssociative d' e' f')}=
>     ( ((m * e + n * d) * f + o * (d * e), (d' * e') * f') )
>   ={ cong {f = \ ZUZU => ((m * e + n * d) * f + o * (ZUZU), (d' * e') * f')}
>           (sym toNatMultLemma) }=
>     ( ((m * e + n * d) * f + o * (toNat (d' * e')), (d' * e') * f') )
>   ={ Refl }=  
>     ( (m * e + n * d, d' * e') + (o, f') )
>   ={ Refl }=
>     ( ((m, d') + (n, e')) + (o, f') )
>   QED
> %freeze plusAssociative


> {-
 
> ||| Reduction yields coprime numbers
> reduceYieldsCoprimes : (x : Fraction) -> Coprime (num (reduce x)) (den (reduce x))
> reduceYieldsCoprimes (m, n') =
>   let n       :  Nat
>               =  toNat n' in  
>   let zLTn    :  (Z `LT` n)
>               =  toNatLTLemma n' in
>   let d       :  Nat
>               =  gcdAlg m n in
>   let dGCDmn  :  (GCD d m n)
>               =  gcdAlgLemma m n in
>   let dDm     :  (d `Divisor` m)
>               =  gcdDivisorFst dGCDmn in
>   let dDn     :  (d `Divisor` n)
>               =  gcdDivisorSnd dGCDmn in
>   let zLTd    :  (Z `LT` d)
>               =  gcdPreservesPositivity2 zLTn (d ** dGCDmn) in
>   gcdCoprimeLemma d m n dDm dDn zLTd dGCDmn
> %freeze reduceYieldsCoprimes


> ||| Reduction of coprime numbers is identity
> reducePreservesCoprimes : (x : Fraction) -> Coprime (num x) (den x) -> reduce x = x                       
> reducePreservesCoprimes (m, n') (MkCoprime prf) =
>   let n       :  Nat
>               =  toNat n' in  
>   let d       :  Nat
>               =  gcdAlg m n in
>   let dGCDmn  :  (GCD d m n)
>               =  gcdAlgLemma m n in 
>   let dDm     :  (d `Divisor` m)
>               =  gcdDivisorFst dGCDmn in
>   let dDn     :  (d `Divisor` n)
>               =  gcdDivisorSnd dGCDmn in
>   let o       :  Nat
>               =  quotient m d dDm in
>   let p       :  Nat
>               =  quotient n d dDn in
>   let zLTn    :  (Z `LT` n)
>               =  toNatLTLemma n' in 
>   let zLTp    :  (Z `LT` p) 
>               =  quotientPreservesPositivity n d dDn zLTn in
>   let dEQ1    :  (d = S Z)
>               =  prf in
>             
>     ( reduce (m, n') )
>   ={ Refl }=
>     ( (o, fromNat p zLTp) )
>   ={ cong2 (quotientAnyOneAny m d dDm dEQ1) (toNatEqLemma (quotientAnyOneAny n d dDn dEQ1)) }=
>     ( (m, n') )
>   QED
> %freeze reducePreservesCoprimes


> ||| Reduction is idempotent (not used)
> reduceIdempotent : (x : Fraction) -> reduce (reduce x) = reduce x
> reduceIdempotent x = 
>     ( reduce (reduce x) )
>   ={ reducePreservesCoprimes (reduce x) (reduceYieldsCoprimes x) }=
>     ( reduce x )
>   QED
> %freeze reduceIdempotent


> ||| 
> reduceQuotientLemma : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                       (m : Nat) -> (n : Nat) -> (d : Nat) ->
>                       (dDm : d `Divisor` m) -> (dDn : d `Divisor` n) ->
>                       reduce alg (m, n) = reduce alg (quotient m d dDm, quotient n d dDn)


> ||| Reduction is "linear"
> reduceLinear : (alg : (m : Nat) -> (n : Nat) -> (d : Nat ** GCD d m n)) -> 
>                (x : Fraction) -> (y : Fraction) ->
>                reduce alg (x + y) = reduce alg (reduce alg x + reduce alg y)
> reduceLinear alg (m, d') (n, e') =
>   let d             :  Nat
>                     =  toNat d' in
>   let e             :  Nat
>                     =  toNat e' in
> {-
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
> -}
>                     
>     ( reduce alg ((m, d') + (n, e')) )
>   ={ Refl }=
>     ( reduce alg (m * e + n * d, d' * e') )
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

 
> ---}

 
