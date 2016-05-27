> module FractionNormalizeProperties

> import Syntax.PreorderReasoning

> import Fraction
> import FractionBasicOperations
> import FractionNormalize
> import FractionPredicates
> import FractionNormal
> import FractionBasicProperties
> import FractionEqProperties
> import FractionLTEProperties
> import PNat
> import PNatOperations
> import PNatProperties
> import NatPositive
> import Basics
> import NatLTEProperties
> import NatLTProperties
> import NatOperationsProperties
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


> {-

> ---}

