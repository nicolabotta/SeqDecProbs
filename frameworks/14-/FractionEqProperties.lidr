> module FractionEqProperties

> import Syntax.PreorderReasoning

> import Fraction
> import FractionBasicOperations
> import FractionPredicates
> import FractionBasicProperties
> import PNat
> import PNatOperations
> import PNatProperties
> import NatLTProperties
> import NatOperationsProperties
> import NatPositive

> %default total
> %access export
> -- %access public export


|Eq| is an equivalence:

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



Properties of |(=)| and |Eq|:

> ||| Equality implies `Eq`
> eqEq : {x, y : Fraction} -> x = y -> x `Eq` y
> eqEq {x = (m, d')} {y = (m, d')} Refl = Refl


Properties of |plus| and |Eq|:

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


Properties of |mult|, |Eq|:

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


Properties of |plus|, |mult|, |Eq|:

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


> {-

> ---}

