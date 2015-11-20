> module FractionProperties

> import Syntax.PreorderReasoning

> import Fraction
> import FractionOperations
> import FractionNormal
> import PNat
> import PNatOperations
> import PNatProperties
> import NatPositive
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


Properties of |plus|:

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
>     ( (n, d') + (0, Element 1 MkPositive) )
>   ={ Refl }=
>     ( (n * 1 + 0 * d, d' * (Element 1 MkPositive)) )
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


Properties of |mult|:

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
>     ( (n, d') * (1, Element 1 MkPositive) )
>   ={ Refl }=
>     ( (n * 1, d' * (Element 1 MkPositive)) )
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


Properties of |normalize|:

> ||| 
> normalNormalize : (x : Fraction) -> Normal (normalize x)
> normalNormalize (m, n') =
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
>   MkNormal (gcdCoprimeLemma d m n dDm dDn zLTd dGCDmn)
> %freeze normalNormalize


> ||| Normalization of normal fraction is identity
> normalizePreservesNormal : (x : Fraction) -> Normal x -> normalize x = x                       
> normalizePreservesNormal (m, n') (MkNormal (MkCoprime prf)) =
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
>     ( normalize (m, n') )
>   ={ Refl }=
>     ( (o, fromNat p zLTp) )
>   ={ cong2 (quotientAnyOneAny m d dDm dEQ1) (toNatEqLemma (quotientAnyOneAny n d dDn dEQ1)) }=
>     ( (m, n') )
>   QED
> %freeze normalizePreservesNormal


> ||| normalize is idempotent
> normalizeIdempotent : (x : Fraction) -> normalize (normalize x) = normalize x
> normalizeIdempotent x = 
>     ( normalize (normalize x) )
>   ={ normalizePreservesNormal (normalize x) (normalNormalize x) }=
>     ( normalize x )
>   QED
> %freeze normalizeIdempotent


> |||
> normalizeUpscaleLemma : (x : Fraction) -> (e : PNat) -> normalize (upscale x e) = normalize x
> normalizeUpscaleLemma (m, d') e' =
>   let d              :  Nat
>                      =  toNat d' in 
>   let g              :  Nat
>                      =  gcdAlg m d in
>   let gmd            :  (GCD g m d)
>                      =  gcdAlgLemma m d in 
>   let gDm            :  (g `Divisor` m)
>                      =  gcdDivisorFst gmd in
>   let gDd            :  (g `Divisor` d)
>                      =  gcdDivisorSnd gmd in
>   let qmg            :  Nat
>                      =  quotient m g gDm in
>   let qdg            :  Nat
>                      =  quotient d g gDd in
>   let zLTd           :  (Z `LT` d)
>                      =  toNatLTLemma d' in 
>   let zLTg           :  (Z `LT` g)
>                      =  gcdPreservesPositivity2 zLTd (g ** gmd) in 
>   let zLTqdg         :  (Z `LT` qdg) 
>                      =  quotientPreservesPositivity d g gDd zLTd in
>   let e              :  Nat
>                      =  toNat e' in
>   let zLTe           :  (Z `LT` e)
>                      =  toNatLTLemma e' in 
>   let ed             :  Nat
>                      =  toNat (e' * d') in
>   let h              :  Nat
>                      =  gcdAlg (e * m) ed in
>   let hemed          :  (GCD h (e * m) ed)
>                      =  gcdAlgLemma (e * m) ed in 
>   let hDem           :  (h `Divisor` (e * m))
>                      =  gcdDivisorFst hemed in
>   let hDed           :  (h `Divisor` ed)
>                      =  gcdDivisorSnd hemed in
>   let qemh           :  Nat
>                      =  quotient (e * m) h hDem in
>   let qedh           :  Nat
>                      =  quotient ed h hDed in
>   let zLTed          :  (Z `LT` ed)
>                      =  toNatLTLemma (e' * d') in 
>   let zLTqedh        :  (Z `LT` qedh) 
>                      =  quotientPreservesPositivity ed h hDed zLTed in

>   let edEQed         :  (toNat (e' * d') = e * d)
>                      =  toNatMultLemma in
>   let hemed'         :  (GCD h (e * m) (e * d))
>                      =  replace {P = \ ZUZU => GCD h (e * m) ZUZU} edEQed hemed in
>   let hEQeg          :  (h = e * g)
>                      =  gcdScaleInvariant g m d h e gmd hemed' in
>   let egemed         :  (GCD (e * g) (e * m) (e * d))
>                      =  replace {P = \ ZUZU => GCD ZUZU (e * m) (e * d)} hEQeg hemed' in 
>   let egDem          :  ((e * g) `Divisor` (e * m))
>                      =  gcdDivisorFst egemed in
>   let egDed          :  ((e * g) `Divisor` (e * d))
>                      =  gcdDivisorSnd egemed in
>   let qemeg          :  Nat
>                      =  quotient (e * m) (e * g) egDem in
>   let qedeg          :  Nat
>                      =  quotient (e * d) (e * g) egDed in
>   let zLTed'         :  (Z `LT` (e * d))
>                      =  multZeroLTZeroLT e d zLTe zLTd in
>   let zLTqedeg       :  (Z `LT` qedeg) 
>                      =  quotientPreservesPositivity (e * d) (e * g) egDed zLTed' in
>   let nhEQZ          :  (Not (h = Z))
>                      =  gtZisnotZ (gcdPreservesPositivity2 zLTed (h ** hemed)) in 
>   let negEQZ         :  (Not (e * g = Z))
>                      =  gtZisnotZ (multZeroLTZeroLT e g zLTe zLTg) in
>   let qemhEQqemeg    :  (qemh = qemeg)
>                      =  quotientEqLemma (e * m) h hDem (e * m) (e * g) egDem Refl hEQeg nhEQZ in
>   let qedhEQqedeg    :  (qedh = qedeg)
>                      =  quotientEqLemma ed h hDed (e * d) (e * g) egDed edEQed hEQeg nhEQZ in
>   let qemegEQqmg     :  (qemeg = qmg)
>                      =  sym (quotientScaleInvariant m g e negEQZ gDm egDem) in
>   let qedegEQqdg     :  (qedeg = qdg)
>                      =  sym (quotientScaleInvariant d g e negEQZ gDd egDed) in
>   let qedh'          :  PNat
>                      =  fromNat qedh zLTqedh in
>   let qedeg'         :  PNat
>                      =  fromNat qedeg zLTqedeg in
>   let qedh'EQqedeg'  :  (qedh' = qedeg')
>                      =  toNatEqLemma {x = fromNat qedh zLTqedh} {y = fromNat qedeg zLTqedeg} qedhEQqedeg in
>   let qdg'           :  PNat
>                      =  fromNat qdg zLTqdg in
>   let qedeg'EQqdg'   :  (qedeg' = qdg')
>                      =  toNatEqLemma {x = fromNat qedeg zLTqedeg} {y = fromNat qdg zLTqdg} qedegEQqdg in
>                 
>     ( normalize (upscale (m, d') e') )
>   ={ Refl }=
>     ( normalize (m * e, d' * e') )
>   ={ cong {f = \ ZUZU => normalize (ZUZU, d' * e')} (multCommutative m e) }=
>     ( normalize (e * m, d' * e') )
>   ={ cong {f = \ ZUZU => normalize (e * m, ZUZU)} (multCommutative d' e') }=
>     ( normalize (e * m, e' * d') )
>   ={ Refl }=
>     ( (qemh, qedh') )
>   ={ cong {f = \ ZUZU => (ZUZU, qedh')} qemhEQqemeg }=
>     ( (qemeg, qedh') )
>   ={ cong {f = \ ZUZU => (qemeg, ZUZU)} qedh'EQqedeg' }=
>     ( (qemeg, qedeg') )
>   ={ cong {f = \ ZUZU => (ZUZU, qedeg')} qemegEQqmg }=
>     ( (qmg, qedeg') )
>   ={ cong {f = \ ZUZU => (qmg, ZUZU)} qedeg'EQqdg' }=
>     ( (qmg, qdg') )
>   ={ Refl }=
>     ( normalize (m, d') )
>   QED


Properties of |Eq|:

> ||| Eq is reflexive
> EqReflexive : {x : Fraction} -> x `Eq` x
> EqReflexive {x = (m, d')} = Refl


> ||| Eq is symmetric
> EqSymmetric : {x, y : Fraction} -> x `Eq` y -> y `Eq` x
> EqSymmetric {x = (m, d')} {y = (n, e')} = sym


> ||| Eq is transitive
> EqTransitive : {x, y, z : Fraction} -> x `Eq` y -> y `Eq` z  -> x `Eq` z
> EqTransitive {x = (m, d')} {y = (n, e')} {z = (o, f')} xy yz = 
>   let d       =  toNat d' in
>   let e       =  toNat e' in
>   let f       =  toNat f' in
>   let neEQZ   :  (Not (e = Z))
>               =  gtZisnotZ (toNatLTLemma e') in
>   let s1      :  ((m * e) * f = (n * d) * f)
>               =  multPreservesEq (m * e) (n * d) f f xy Refl in  
>   let s2      :  (m * (e * f) = (n * d) * f)
>               =  replace {P = \ ZUZU => ZUZU = (n * d) * f} (sym (multAssociative m e f)) s1 in
>   let s3      :  (m * (f * e) = (n * d) * f)
>               =  replace {P = \ ZUZU => m * ZUZU = (n * d) * f} (multCommutative e f) s2 in
>   let s4      :  ((m * f) * e = (n * d) * f)
>               =  replace {P = \ ZUZU => ZUZU = (n * d) * f} (multAssociative m f e) s3 in
>   let s5      :  ((m * f) * e = n * (d * f))
>               =  replace {P = \ ZUZU => (m * f) * e = ZUZU} (sym (multAssociative n d f)) s4 in
>   let s6      :  ((m * f) * e = n * (f * d))
>               =  replace {P = \ ZUZU => (m * f) * e = n * ZUZU} (multCommutative d f) s5 in
>   let s7      :  ((m * f) * e = (n * f) * d)
>               =  replace {P = \ ZUZU => (m * f) * e = ZUZU} (multAssociative n f d) s6 in
>   let s8      :  ((m * f) * e = (o * e) * d)
>               =  replace {P = \ ZUZU => (m * f) * e = ZUZU * d} yz s7 in  
>   let s9      :  ((m * f) * e = o * (e * d))
>               =  replace {P = \ ZUZU => (m * f) * e = ZUZU} (sym (multAssociative o e d)) s8 in
>   let s10     :  ((m * f) * e = o * (d * e))
>               =  replace {P = \ ZUZU => (m * f) * e = o * ZUZU} (multCommutative e d) s9 in
>   let s11     :  ((m * f) * e = (o * d) * e)
>               =  replace {P = \ ZUZU => (m * f) * e = ZUZU} (multAssociative o d e) s10 in
>
>   multMultElimRight (m * f) (o * d) e e Refl neEQZ s11


Properties of |Eq|, |plus|:

> |||
> plusPreservesEq : (x, x', y, y' : Fraction) -> 
>                   (x `Eq` x') -> (y `Eq` y') -> (x + y) `Eq` (x' + y')
> plusPreservesEq (n, Element d _) (n', Element d' _) 
>                 (m, Element e _) (m', Element e' _) 
>                 nd'EQn'd me'EQm'e = pf where
>   helper : (a, b, c, d : Nat) -> (a * b) * (c * d) = (a * c) * (b * d)
>   helper a b c d =
>     ((a * b) * (c * d))  ={ sym (multAssociative a b (c * d))                    }=
>     (a * (b * (c * d)))  ={ cong {f = \x => a * x} (multAssociative b c d)       }=
>     (a * ((b * c) * d))  ={ cong {f = \x => a * (x * d)} (multCommutative b c)   }=
>     (a * ((c * b) * d))  ={ cong {f = \x => a * x} (sym (multAssociative c b d)) }=
>     (a * (c * (b * d)))  ={ multAssociative a c (b * d)                          }=
>     ((a * c) * (b * d))  QED
>   helper2 : (a, b, c, d, a', c' : Nat) -> (a * c = a' * c') ->
>             ((a * b) * (c * d)) = ((a' * d) * (c' * b))
>   helper2 a b c d a' c' acEQa'c' =
>     ((a * b) * (c * d))   ={ helper a b c d }=
>     ((a * c) * (b * d))   ={ cong {f = \x => x * (b * d)} acEQa'c' }=
>     ((a' * c') * (b * d)) ={ cong {f = \x => (a' * c') * x} (multCommutative b d) }=
>     ((a' * c') * (d * b)) ={ helper a' c' d b }=
>     ((a' * d) * (c' * b)) QED 
>   pf : ((n * e) + (m * d)) * (d' * e') = ((n' * e') + (m' * d')) * (d * e)
>   pf = 
>     (((n * e) + (m * d)) * (d' * e')) 
>       ={ multDistributesOverPlusLeft (n * e) (m * d) (d' * e') }=
>     (((n * e) * (d' * e')) + ((m * d) * (d' * e')))
>       ={ cong {f = \x => x + ((m * d) * (d' * e'))} (helper2 n e d' e' n' d nd'EQn'd) }=
>     (((n' * e') * (d * e)) + ((m * d) * (d' * e')))
>       ={ cong {f = \x => ((n' * e') * (d * e)) + ((m * d) * x)} (multCommutative d' e') }=
>     (((n' * e') * (d * e)) + ((m * d) * (e' * d')))
>       ={ cong {f = \x => ((n' * e') * (d * e)) + x} (helper2 m d e' d' m' e me'EQm'e) }=
>     (((n' * e') * (d * e)) + ((m' * d') * (e * d)))
>       ={ cong {f = \x => ((n' * e') * (d * e)) + ((m' * d') * x)} (multCommutative e d) }=
>     (((n' * e') * (d * e)) + ((m' * d') * (d * e)))
>       ={ sym (multDistributesOverPlusLeft (n' * e') (m' * d') (d * e)) }=
>     (((n' * e') + (m' * d')) * (d * e))
>       QED


Properties of |Eq|, |mult|:

> ||| 
> multPreservesEq : (x, x' : Fraction) -> (x `Eq` x') -> 
>                   (y, y' : Fraction) -> (y `Eq` y') ->
>                   (x * y) `Eq` (x' * y')
> multPreservesEq (n, Element d _) (n', Element d' _) nd'EQn'd
>                 (m, Element e _) (m', Element e' _) me'EQm'e = pf where
>   helper : (a, b, c, d : Nat) -> (a * b) * (c * d) = (a * c) * (b * d)
>   helper a b c d =
>     ((a * b) * (c * d))  ={ sym (multAssociative a b (c * d))                    }=
>     (a * (b * (c * d)))  ={ cong {f = \x => a * x} (multAssociative b c d)       }=
>     (a * ((b * c) * d))  ={ cong {f = \x => a * (x * d)} (multCommutative b c)   }=
>     (a * ((c * b) * d))  ={ cong {f = \x => a * x} (sym (multAssociative c b d)) }=
>     (a * (c * (b * d)))  ={ multAssociative a c (b * d)                          }=
>     ((a * c) * (b * d))  QED
>   pf : (n * m) * (d' * e') = (n' * m') * (d * e)
>   pf = 
>     ((n * m) * (d' * e')) ={ helper n m d' e' }=
>     ((n * d') * (m * e')) ={ cong {f = \x => x * (m * e')} nd'EQn'd }=
>     ((n' * d) * (m * e')) ={ cong {f = \x => (n' * d) * x} me'EQm'e }=
>     ((n' * d) * (m' * e)) ={ helper n' d m' e }=
>     ((n' * m') * (d * e)) QED


Properties of |normalize|, |Eq|:

> |||
> normalizeEqLemma1 : (x : Fraction) -> (normalize x) `Eq` x
> normalizeEqLemma1 (m, n') =
>   let n     :  Nat
>             =  toNat n' in 
>   let d     :  Nat
>             =  gcdAlg m n in
>   let v     :  (GCD d m n)
>             =  gcdAlgLemma m n in 
>   let dDm   :  (d `Divisor` m)
>             =  gcdDivisorFst v in
>   let dDn   :  (d `Divisor` n)
>             =  gcdDivisorSnd v in
> 
>  flipQuotientLemma m n d dDm dDn


> |||
> normalizeEqLemma2 : (x : Fraction) -> (y : Fraction) -> 
>                     x `Eq` y -> normalize x = normalize y
> normalizeEqLemma2 (m1, n1') (m2, n2') m1n2EQm2n1 =                    
>   let n1  =  toNat n1' in
>   let n2  =  toNat n2' in
>   
>     ( normalize (m1, n1') )
>   ={ sym (normalizeUpscaleLemma (m1, n1') n2') }=
>     ( normalize (m1 * n2, n1' * n2') )
>   ={ cong {f = \ ZUZU => normalize (ZUZU, n1' * n2')} m1n2EQm2n1 }=
>     ( normalize (m2 * n1, n1' * n2') )
>   ={ cong {f = \ ZUZU => normalize (m2 * n1, ZUZU)} (multCommutative n1' n2') }=
>     ( normalize (m2 * n1, n2' * n1') )
>   ={ normalizeUpscaleLemma (m2, n2') n1' }=
>     ( normalize (m2, n2') )
>   QED

> {-

> ---}

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

 
