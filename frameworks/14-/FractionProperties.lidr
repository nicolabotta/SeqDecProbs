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


> ||| 0 is neutral element of addition
> plusZeroRightNeutral : (x : Fraction) -> x + 0 = x
> plusZeroRightNeutral (n, d') =
>   let d = toNat d' in
>     ( (n, d') + 0 )
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


> ||| 0 is neutral element of addition
> plusZeroLeftNeutral  : (x : Fraction) -> 0 + x = x
> plusZeroLeftNeutral x = 
>     ( 0 + x )
>   ={ plusCommutative 0 x }=
>     ( x + 0 )
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


> ||| 1 is neutral element of multiplication
> multOneRightNeutral : (x : Fraction) -> x * 1 = x
> multOneRightNeutral (n, d') =
>   let d = toNat d' in
>     ( (n, d') * 1 )
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


> ||| 1 is neutral element of multiplication
> multOneLeftNeutral  : (x : Fraction) -> 1 * x = x
> multOneLeftNeutral x = 
>     ( 1 * x )
>   ={ multCommutative 1 x }=
>     ( x * 1 )
>   ={ multOneRightNeutral x }=
>     ( x )
>   QED
> %freeze multOneLeftNeutral


Basic properties of |normalize|:

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
> %freeze normalizeUpscaleLemma

Properties of |Eq|:

> ||| Eq is reflexive
> EqReflexive : {x : Fraction} -> x `Eq` x
> EqReflexive {x = (m, d')} = Refl
> %freeze EqReflexive


> ||| Eq is symmetric
> EqSymmetric : {x, y : Fraction} -> x `Eq` y -> y `Eq` x
> EqSymmetric {x = (m, d')} {y = (n, e')} = sym
> %freeze EqSymmetric


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
> %freeze EqTransitive


Properties of |Eq|, |plus|:

> |||
> plusPreservesEq : (x, x', y, y' : Fraction) -> 
>                   (x `Eq` x') -> (y `Eq` y') -> (x + y) `Eq` (x' + y')
> plusPreservesEq (n, Element d _) (n', Element d' _) 
>                 (m, Element e _) (m', Element e' _) 
>                 nd'EQn'd me'EQm'e = pf where
>   helper2 : (a, b, c, d, a', c' : Nat) -> (a * c = a' * c') ->
>             ((a * b) * (c * d)) = ((a' * d) * (c' * b))
>   helper2 a b c d a' c' acEQa'c' =
>     ((a * b) * (c * d))   ={ multFlipCentre a b c d }=
>     ((a * c) * (b * d))   ={ cong {f = \x => x * (b * d)} acEQa'c' }=
>     ((a' * c') * (b * d)) ={ cong {f = \x => (a' * c') * x} (multCommutative b d) }=
>     ((a' * c') * (d * b)) ={ multFlipCentre a' c' d b }=
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
> %freeze plusPreservesEq


Properties of |Eq|, |mult|:

> ||| 
> multPreservesEq : (x, x', y, y' : Fraction) -> 
>                   (x `Eq` x') -> (y `Eq` y') -> (x * y) `Eq` (x' * y')
> multPreservesEq (n, Element d _) (n', Element d' _) 
>                 (m, Element e _) (m', Element e' _) 
>                 nd'EQn'd me'EQm'e = pf where
>   pf : (n * m) * (d' * e') = (n' * m') * (d * e)
>   pf = 
>     ((n * m) * (d' * e')) ={ multFlipCentre n m d' e' }=
>     ((n * d') * (m * e')) ={ cong {f = \x => x * (m * e')} nd'EQn'd }=
>     ((n' * d) * (m * e')) ={ cong {f = \x => (n' * d) * x} me'EQm'e }=
>     ((n' * d) * (m' * e)) ={ multFlipCentre n' d m' e }=
>     ((n' * m') * (d * e)) QED
> %freeze multPreservesEq


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
> %freeze normalizeEqLemma1


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
> %freeze normalizeEqLemma2


Further properties of |normalize|:

> |||
> normalizePlusElimLeft : (x : Fraction) -> (y : Fraction) -> 
>                         normalize (normalize x + y) = normalize (x + y)
> normalizePlusElimLeft x y = 
>   let nxEqx   = normalizeEqLemma1 x in
>   let nxyEqxy = plusPreservesEq (normalize x) x y y nxEqx EqReflexive in
>   normalizeEqLemma2 (normalize x + y) (x + y) nxyEqxy
> %freeze normalizePlusElimLeft


> |||
> normalizePlusElimRight : (x : Fraction) -> (y : Fraction) -> 
>                          normalize (x + normalize y) = normalize (x + y)
> normalizePlusElimRight x y = 
>   let nyEqy   = normalizeEqLemma1 y in
>   let xnyEqxy = plusPreservesEq x x (normalize y) y EqReflexive nyEqy in
>   normalizeEqLemma2 (x + normalize y) (x + y) xnyEqxy
> %freeze normalizePlusElimRight


> |||
> normalizePlusElim : (x : Fraction) -> (y : Fraction) -> 
>                     normalize (normalize x + normalize y) = normalize (x + y)
> normalizePlusElim x y = 
>   let nxEqx   = normalizeEqLemma1 x in
>   let nyEqy   = normalizeEqLemma1 y in
>   let nxnyEqxy = plusPreservesEq (normalize x) x (normalize y) y nxEqx nyEqy in
>   normalizeEqLemma2 (normalize x + normalize y) (x + y) nxnyEqxy
> %freeze normalizePlusElim


> {-

> ---}

