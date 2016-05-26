> module FractionProperties

> import Syntax.PreorderReasoning

> import Fraction
> import FractionOperations
> import FractionPredicates
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
> import PairsOperations
> import Sigma


> %default total

> %access public export
> -- %access export


> ||| Denominators of fractions are greater than zero
> denLTLemma : (x : Fraction) -> Z `LT` den x
> denLTLemma x = s2 where
>   s1 : Z `LT` toNat (snd x)
>   s1 = toNatLTLemma (snd x)
>   s2 : Z `LT` den x
>   s2 = replace {P = \ ZUZU => Z `LT` ZUZU} Refl s1

> |||
> fromNatNormal : {n : Nat} -> Normal (fromNat n)
> fromNatNormal = MkNormal anyCoprimeOne
> %freeze fromNatNormal


> {-
> ||| Fraction is an instance of Show
> instance Show Fraction where
>   show q = show (num q) ++ "/" ++ show (den q)
> -}


> ||| Fraction is an instance of Num
> implementation Num Fraction where
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
>               =  gcdPreservesPositivity2 zLTn (MkSigma d dGCDmn) in
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
>                      =  gcdPreservesPositivity2 zLTd (MkSigma g gmd) in 
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
>                      =  gtZisnotZ (gcdPreservesPositivity2 zLTed (MkSigma h hemed)) in 
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


> |||
> eqEq : {x, y : Fraction} -> x = y -> x `Eq` y
> eqEq {x = (m, d')} {y = (m, d')} Refl = Refl


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
> multZeroRightEqZero : (x : Fraction) -> x * 0 `Eq` 0
> multZeroRightEqZero (m, d') =
>   let d = toNat d' in
>     ( (m * 0) * 1 )
>   ={ cong {f = \ ZUZU => ZUZU * 1} (multZeroRightZero m) }=
>     ( 0 * 1 )
>   ={ multZeroLeftZero 1 }=  
>     ( 0 )  
>   ={ sym (multZeroLeftZero (d * 1)) }=
>     ( 0 * (d * 1) )
>   QED 
> %freeze multZeroRightEqZero


> |||
> multZeroLeftEqZero : (x : Fraction) -> 0 * x `Eq` 0
> multZeroLeftEqZero x = 
>   let zxEqxz  : (0 * x `Eq` x * 0)
>               = eqEq (multCommutative 0 x) in
>   let xzEqz   : (x * 0 `Eq` 0)
>               = multZeroRightEqZero x in
>   EqTransitive zxEqxz xzEqz


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


Properties of |Eq|, |plus|, |mult|:

> |||
> multDistributesOverPlusRightEq : {x, y, z : Fraction} -> x * (y + z) `Eq` (x * y) + (x * z)
> multDistributesOverPlusRightEq {x = (m, d')} {y = (n, e')} {z = (o, f')} = 
>   let d       =  toNat d' in
>   let e       =  toNat e' in
>   let f       =  toNat f' in
>     ( (m * (n * f + o * e)) * (toNat ((d' * e') * (d' * f'))) )
>   ={ cong {f = \ ZUZU => (m * (n * f + o * e)) * ZUZU} toNatMultLemma }=
>     ( (m * (n * f + o * e)) * ((toNat (d' * e')) * (toNat (d' * f'))) )
>   ={ cong {f = \ ZUZU => (m * (n * f + o * e)) * (ZUZU * (toNat (d' * f')))} toNatMultLemma }=
>     ( (m * (n * f + o * e)) * ((d * e) * (toNat (d' * f'))) )  
>   ={ cong {f = \ ZUZU => (m * (n * f + o * e)) * ((d * e) * ZUZU)} toNatMultLemma }=
>     ( (m * (n * f + o * e)) * ((d * e) * (d * f)) )  
>   ={ cong {f = \ ZUZU => (m * (n * f + o * e)) * ZUZU} (multFlipCentre d e d f) }=
>     ( (m * (n * f + o * e)) * ((d * d) * (e * f)) )  
>   ={ cong {f = \ ZUZU => (m * (n * f + o * e)) * ZUZU} (sym (multAssociative d d (e * f))) }=
>     ( (m * (n * f + o * e)) * (d * (d * (e * f))) )  
>   ={ multAssociative (m * (n * f + o * e)) d (d * (e * f)) }=
>     ( ((m * (n * f + o * e)) * d) * (d * (e * f)) )  
>   ={ cong {f = \ ZUZU => (ZUZU * d) * (d * (e * f))} (multDistributesOverPlusRight m (n * f) (o * e)) }=
>     ( ((m * (n * f) + m * (o * e)) * d) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => ((ZUZU + m * (o * e)) * d) * (d * (e * f))} (multAssociative m n f) }=
>     ( (((m * n) * f + m * (o * e)) * d) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => (((m * n) * f + ZUZU) * d) * (d * (e * f))} (multAssociative m o e) }=  
>     ( (((m * n) * f + (m * o) * e) * d) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => ZUZU * (d * (e * f))} (multDistributesOverPlusLeft ((m * n) * f) ((m * o) * e) d)}=  
>     ( (((m * n) * f) * d + ((m * o) * e) * d) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => (ZUZU + ((m * o) * e) * d) * (d * (e * f))} (sym (multAssociative (m * n) f d)) }=
>     ( ((m * n) * (f * d) + ((m * o) * e) * d) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => ((m * n) * (f * d) + ZUZU) * (d * (e * f))} (sym (multAssociative (m * o) e d)) }=  
>     ( ((m * n) * (f * d) + (m * o) * (e * d)) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => ((m * n) * (f * d) + (m * o) * ZUZU) * (d * (e * f))} (multCommutative e d) }=
>     ( ((m * n) * (f * d) + (m * o) * (d * e)) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => ((m * n) * ZUZU + (m * o) * (d * e)) * (d * (e * f))} (multCommutative f d) }=
>     ( ((m * n) * (d * f) + (m * o) * (d * e)) * (d * (e * f)) )
>   ={ cong {f = \ ZUZU => ((m * n) * (d * f) + (m * o) * (d * e)) * (d * ZUZU)} (sym toNatMultLemma) }=  
>     ( ((m * n) * (d * f) + (m * o) * (d * e)) * (d * (toNat (e' * f'))) )
>   ={ cong {f = \ ZUZU => ((m * n) * (d * f) + (m * o) * (d * e)) * ZUZU}  (sym toNatMultLemma) }=  
>     ( ((m * n) * (d * f) + (m * o) * (d * e)) * (toNat (d' * (e' * f'))) )
>   ={ cong {f = \ ZUZU => ((m * n) * (d * f) + (m * o) * ZUZU) * (toNat (d' * (e' * f')))} 
>           (sym toNatMultLemma) }=
>     ( ((m * n) * (d * f) + (m * o) * (toNat (d' * e'))) * (toNat (d' * (e' * f'))) )
>   ={ cong {f = \ ZUZU => ((m * n) * ZUZU + (m * o) * (toNat (d' * e'))) * (toNat (d' * (e' * f')))} 
>           (sym toNatMultLemma) }=
>     ( ((m * n) * (toNat (d' * f')) + (m * o) * (toNat (d' * e'))) * (toNat (d' * (e' * f'))) )
>   QED
> %freeze multDistributesOverPlusRightEq


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


> |||
> normalizeMultElimLeft : (x : Fraction) -> (y : Fraction) -> 
>                         normalize ((normalize x) * y) = normalize (x * y)
> normalizeMultElimLeft x y = 
>   let nxEqx   = normalizeEqLemma1 x in
>   let nxyEqxy = multPreservesEq (normalize x) x y y nxEqx EqReflexive in
>   normalizeEqLemma2 ((normalize x) * y) (x * y) nxyEqxy
> %freeze normalizeMultElimLeft


> |||
> normalizeMultElimRight : (x : Fraction) -> (y : Fraction) -> 
>                          normalize (x * (normalize y)) = normalize (x * y)
> normalizeMultElimRight x y = 
>   let nyEqy   = normalizeEqLemma1 y in
>   let xnyEqxy = multPreservesEq x x (normalize y) y EqReflexive nyEqy in
>   normalizeEqLemma2 (x * (normalize y)) (x * y) xnyEqxy
> %freeze normalizeMultElimRight


> |||
> normalizeMultElim : (x : Fraction) -> (y : Fraction) -> 
>                     normalize ((normalize x) * (normalize y)) = normalize (x * y)
> normalizeMultElim x y = 
>   let nxEqx   = normalizeEqLemma1 x in
>   let nyEqy   = normalizeEqLemma1 y in
>   let nxnyEqxy = multPreservesEq (normalize x) x (normalize y) y nxEqx nyEqy in
>   normalizeEqLemma2 ((normalize x) * (normalize y)) (x * y) nxnyEqxy
> %freeze normalizeMultElim


> |||
> normalizeLTELemma : (x : Fraction) -> (y : Fraction) -> 
>                     x `LTE` y -> normalize x `LTE` normalize y
> normalizeLTELemma (nx, dx') (ny, dy') xLTEy = s11 where
> 
>   dx  : Nat
>   dx  = toNat dx'
>   zLTdx : Z `LT` dx
>   zLTdx = toNatLTLemma dx'
>   
>   dy  : Nat
>   dy  = toNat dy'
>   zLTdy : Z `LT` dy
>   zLTdy = toNatLTLemma dy'
>   
>   gx  : Nat
>   gx  = gcdAlg nx dx
>   pgx : GCD gx nx dx
>   pgx = gcdAlgLemma nx dx
>   gxDnx : gx `Divisor` nx
>   gxDnx = gcdDivisorFst pgx
>   gxDdx : gx `Divisor` dx
>   gxDdx = gcdDivisorSnd pgx
>   zLTgx : Z `LT` gx
>   zLTgx = gcdPreservesPositivity2 zLTdx (MkSigma gx pgx)
>   
>   gy  : Nat
>   gy  = gcdAlg ny dy
>   pgy : GCD gy ny dy
>   pgy = gcdAlgLemma ny dy
>   gyDny : gy `Divisor` ny
>   gyDny = gcdDivisorFst pgy
>   gyDdy : gy `Divisor` dy
>   gyDdy = gcdDivisorSnd pgy
>   zLTgy : Z `LT` gy
>   zLTgy = gcdPreservesPositivity2 zLTdy (MkSigma gy pgy)
>   
>   nnx : Nat
>   nnx = quotient nx gx gxDnx
>   dnx : Nat
>   dnx = quotient dx gx gxDdx
>   zLTdnx : Z `LT` dnx
>   zLTdnx = quotientPreservesPositivity dx gx gxDdx zLTdx
>   dnx' : PNat
>   dnx' = fromNat dnx zLTdnx
>   
>   nny : Nat
>   nny = quotient ny gy gyDny
>   dny : Nat
>   dny = quotient dy gy gyDdy
>   zLTdny : Z `LT` dny
>   zLTdny = quotientPreservesPositivity dy gy gyDdy zLTdy
>   dny' : PNat
>   dny' = fromNat dny zLTdny
>   
>   nxdy : Nat
>   nxdy = nx * dy
>   nydx : Nat
>   nydx = ny * dx
>   gxgy : Nat
>   gxgy = gx * gy
>   gygx : Nat
>   gygx = gy * gx
>   gxgyDnxdy : gxgy `Divisor` nxdy
>   gxgyDnxdy = divisorMultLemma1 nx gx gxDnx dy gy gyDdy
>   gygxDnydx : gygx `Divisor` nydx 
>   gygxDnydx = divisorMultLemma1 ny gy gyDny dx gx gxDdx
>   ngxgyZ : Not (gxgy = Z)
>   ngxgyZ = multNotZeroNotZero gx gy (gtZisnotZ zLTgx) (gtZisnotZ zLTgy)

>   s01 : LTE nxdy nydx
>   s01 = xLTEy
>   s02 : LTE ((quotient nxdy gxgy gxgyDnxdy) * gxgy) nydx
>   s02 = replace {P = \ ZUZ => LTE ZUZ nydx} 
>                 (sym (quotientLemma' nxdy gxgy gxgyDnxdy)) s01
>   s03 : LTE ((quotient nxdy gxgy gxgyDnxdy) * gxgy) ((quotient nydx gygx gygxDnydx) * gygx)
>   s03 = replace {P = \ ZUZ => LTE ((quotient nxdy gxgy gxgyDnxdy) * gxgy) ZUZ} 
>                 (sym (quotientLemma' nydx gygx gygxDnydx)) s02
>   s04 : LTE (quotient nxdy gxgy gxgyDnxdy) (quotient nydx gygx gygxDnydx)
>   s04 = elimRightMultLTE s03 (multCommutative gx gy) ngxgyZ
>   s05 : LTE ((quotient nx gx gxDnx) * (quotient dy gy gyDdy)) (quotient nydx gygx gygxDnydx)                         
>   s05 = replace {P = \ ZUZ => LTE ZUZ (quotient nydx gygx gygxDnydx)} 
>                 (sym (quotientMultLemma nx gx gxDnx dy gy gyDdy)) s04
>   s06 : LTE ((quotient nx gx gxDnx) * (quotient dy gy gyDdy)) ((quotient ny gy gyDny) * (quotient dx gx gxDdx))
>   s06 = replace {P = \ ZUZ => LTE ((quotient nx gx gxDnx) * (quotient dy gy gyDdy)) ZUZ} 
>                 (sym (quotientMultLemma ny gy gyDny dx gx gxDdx)) s05
>   s07 : LTE (nnx * dny) (nny * dnx)
>   s07 = s06
>   s08 : LTE (nnx * (toNat dny')) (nny * dnx)
>   s08 = replace {P = \ ZUZ => LTE (nnx * ZUZ) (nny * dnx)} (sym (toNatfromNatLemma dny zLTdny)) s07
>   s09 : LTE (nnx * (toNat dny')) (nny * (toNat dnx'))
>   s09 = replace {P = \ ZUZ => LTE (nnx * (toNat dny')) (nny * ZUZ)} (sym (toNatfromNatLemma dnx zLTdnx)) s08
>   s10 : (nnx, dnx') `LTE` (nny, dny')
>   s10 = s09
>   s11 : normalize (nx, dx') `LTE` normalize (ny, dy')
>   s11 = s10
> %freeze normalizeLTELemma


Properties of |LTE|:

> ||| LTE is reflexive
> reflexiveLTE : (x : Fraction) -> x `LTE` x
> reflexiveLTE (n, d') = NatProperties.reflexiveLTE (n * (toNat d'))
> %freeze reflexiveLTE


> ||| LTE is transitive
> transitiveLTE : (x, y, z : Fraction) -> x `LTE` y -> y `LTE` z -> x `LTE` z
> transitiveLTE (nx, dx') (ny, dy') (nz, dz') xLTEy yLTEz = s8 where
>   dx : Nat
>   dx = toNat dx'
>   dy : Nat
>   dy = toNat dy'
>   dz : Nat
>   dz = toNat dz'
>   s1    : Prelude.Nat.LTE ((nx * dy) * dz) ((ny * dx) * dz)
>   s1    = monotoneNatMultLTE xLTEy (NatProperties.reflexiveLTE dz)
>   s2    : Prelude.Nat.LTE ((ny * dz) * dx) ((nz * dy) * dx)
>   s2    = monotoneNatMultLTE yLTEz (NatProperties.reflexiveLTE dx)
>   s3    : Prelude.Nat.LTE ((ny * dx) * dz) ((nz * dy) * dx)
>   s3    = replace {P = \ ZUZ => Prelude.Nat.LTE ZUZ ((nz * dy) * dx)} (multSwapRight ny dz dx) s2
>   s4    : Prelude.Nat.LTE ((nx * dy) * dz) ((nz * dy) * dx)
>   s4    = NatProperties.transitiveLTE ((nx * dy) * dz)
>                                       ((ny * dx) * dz)
>                                       ((nz * dy) * dx)
>                                       s1 s3
>   s5    : Prelude.Nat.LTE ((nx * dz) * dy) ((nz * dy) * dx)
>   s5    = replace {P = \ ZUZ => Prelude.Nat.LTE ZUZ ((nz * dy) * dx)} (multSwapRight nx dy dz) s4
>   s6    : Prelude.Nat.LTE ((nx * dz) * dy) ((nz * dx) * dy)
>   s6    = replace {P = \ ZUZ => Prelude.Nat.LTE ((nx * dz) * dy) ZUZ} (multSwapRight nz dy dx) s5
>   s7    : Prelude.Nat.LTE (nx * dz) (nz * dx)
>   s7    = elimRightMultLTE {a = nx * dz} {b = nz * dx} {c = dy} {d = dy}
>                            s6 Refl (gtZisnotZ (denLTLemma (ny, dy')))
>   s8 : (nx, dx') `LTE` (nz, dz')
>   s8 = s7
> %freeze transitiveLTE

                        
> ||| LTE is total
> totalLTE : (x, y : Fraction) -> Either (x `LTE` y) (y `LTE` x) 
> totalLTE (n1, d1') (n2, d2') = 
>   let d1 = toNat d1' in
>   let d2 = toNat d2' in
>   NatProperties.totalLTE (n1 * d2) (n2 * d1)
> %freeze totalLTE


> ||| LTE is monotone w.r.t. `plus`
> monotonePlusLTE : {a, b, c, d : Fraction} -> 
>                   a `LTE` b -> c `LTE` d -> (a `plus` c) `LTE` (b `plus` d)
> monotonePlusLTE {a = (na, da')} {b = (nb, db')} {c = (nc, dc')} {d = (nd, dd')} aLTEb cLTEd = s16 where
>   da : Nat
>   da = toNat da'
>   db : Nat
>   db = toNat db'
>   dc : Nat
>   dc = toNat dc'
>   dd : Nat
>   dd = toNat dd'
>   s1 : Prelude.Nat.LTE (na * db) (nb * da)
>   s1 = aLTEb
>   s2 : Prelude.Nat.LTE (nc * dd) (nd * dc)
>   s2 = cLTEd
>   s3 : Prelude.Nat.LTE ((na * db) * (dc * dd)) ((nb * da) * (dc * dd))
>   s3 = monotoneNatMultLTE s1 (NatProperties.reflexiveLTE (dc * dd))
>   s4 : Prelude.Nat.LTE ((nc * dd) * (da * db)) ((nd * dc) * (da * db))
>   s4 = monotoneNatMultLTE s2 (NatProperties.reflexiveLTE (da * db))
>   s5 : Prelude.Nat.LTE ((na * db) * (dc * dd) + (nc * dd) * (da * db)) 
>                        ((nb * da) * (dc * dd) + (nd * dc) * (da * db))
>   s5 = monotoneNatPlusLTE s3 s4 
>   s6 : Prelude.Nat.LTE ((na * dc) * (db * dd) + (nc * dd) * (da * db)) 
>                        ((nb * da) * (dc * dd) + (nd * dc) * (da * db))
>   s6 = replace {P = \ ZUZ => Prelude.Nat.LTE (         ZUZ          + (nc * dd) * (da * db)) 
>                                              ((nb * da) * (dc * dd) + (nd * dc) * (da * db))} 
>                (multSwap23 na db dc dd) s5 
>   s7 : Prelude.Nat.LTE ((na * dc) * (db * dd) + (nc * da) * (dd * db)) 
>                        ((nb * da) * (dc * dd) + (nd * dc) * (da * db))
>   s7 = replace {P = \ ZUZ => Prelude.Nat.LTE ((na * dc) * (db * dd) +          ZUZ         ) 
>                                              ((nb * da) * (dc * dd) + (nd * dc) * (da * db))} 
>                (multSwap23 nc dd da db) s6
>   s8 : Prelude.Nat.LTE ((na * dc) * (db * dd) + (nc * da) * (dd * db)) 
>                        ((nb * dd) * (dc * da) + (nd * dc) * (da * db))
>   s8 = replace {P = \ ZUZ => Prelude.Nat.LTE ((na * dc) * (db * dd) + (nc * da) * (dd * db)) 
>                                              (         ZUZ          + (nd * dc) * (da * db))} 
>                (multSwap24 nb da dc dd) s7
>   s9 : Prelude.Nat.LTE ((na * dc) * (db * dd) + (nc * da) * (dd * db)) 
>                        ((nb * dd) * (dc * da) + (nd * db) * (da * dc))
>   s9 = replace {P = \ ZUZ => Prelude.Nat.LTE ((na * dc) * (db * dd) + (nc * da) * (dd * db)) 
>                                              ((nb * dd) * (dc * da) +          ZUZ         )} 
>                (multSwap24 nd dc da db) s8                
>   s10 : Prelude.Nat.LTE ((na * dc) * (db * dd) + (nc * da) * (db * dd)) 
>                         ((nb * dd) * (dc * da) + (nd * db) * (da * dc))
>   s10 = replace {P = \ ZUZ => Prelude.Nat.LTE ((na * dc) * (db * dd) + (nc * da) *    ZUZ   ) 
>                                               ((nb * dd) * (dc * da) + (nd * db) * (da * dc))} 
>                 (multCommutative dd db) s9
>   s11 : Prelude.Nat.LTE ((na * dc) * (db * dd) + (nc * da) * (db * dd)) 
>                         ((nb * dd) * (da * dc) + (nd * db) * (da * dc))
>   s11 = replace {P = \ ZUZ => Prelude.Nat.LTE ((na * dc) * (db * dd) + (nc * da) * (db * dd)) 
>                                               ((nb * dd) *    ZUZ    + (nd * db) * (da * dc))} 
>                 (multCommutative dc da) s10
>   s12 : Prelude.Nat.LTE ((na * dc + nc * da) * (db * dd)) 
>                         ((nb * dd) * (da * dc) + (nd * db) * (da * dc))
>   s12 = replace {P = \ ZUZ => Prelude.Nat.LTE ZUZ ((nb * dd) * (da * dc) + (nd * db) * (da * dc))} 
>                 (sym (multDistributesOverPlusLeft (na * dc) (nc * da) (db * dd))) s11
>   s13 : Prelude.Nat.LTE ((na * dc + nc * da) * (db * dd)) ((nb * dd + nd * db) * (da * dc))
>   s13 = replace {P = \ ZUZ => Prelude.Nat.LTE (((na * dc) + (nc * da)) * (db * dd)) ZUZ} 
>                 (sym (multDistributesOverPlusLeft (nb * dd) (nd * db) (da * dc))) s12
>   s14 : Prelude.Nat.LTE ((na * dc + nc * da) * (toNat (db' * dd'))) ((nb * dd + nd * db) * (da * dc))
>   s14 = replace {P = \ ZUZ => Prelude.Nat.LTE ((na * dc + nc * da) * ZUZ) ((nb * dd + nd * db) * (da * dc))} 
>                 (sym toNatMultLemma) s13
>   s15 : Prelude.Nat.LTE ((na * dc + nc * da) * (toNat (db' * dd'))) ((nb * dd + nd * db) * (toNat (da' * dc')))
>   s15 = replace {P = \ ZUZ => Prelude.Nat.LTE ((na * dc + nc * da) * (toNat (db' * dd'))) ((nb * dd + nd * db) * ZUZ)}
>                 (sym toNatMultLemma) s14
>   s16 : ((na, da') `plus` (nc, dc')) `LTE` ((nb, db') `plus` (nd, dd'))
>   s16 = s15
> %freeze monotonePlusLTE


> ||| LTE is monotone w.r.t. `(*)`
> monotoneMultLTE : {a, b, c, d : Fraction} -> 
>                   a `LTE` b -> c `LTE` d -> (a `mult` c) `LTE` (b `mult` d)


> {-

> ---}

