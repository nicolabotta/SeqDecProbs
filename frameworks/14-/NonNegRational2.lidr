> module NonNegRational2

> import NatPositive
> import PNat
> import Fraction as F
> import FractionOperations as FO
> import FractionProperties as FP
> import SplitQuotient as SQ
> import KernelQuotient as KQ
> import Syntax.PreorderReasoning
> import NumRefinements

> %default total

> %access public export


> SQ.Base = F.Fraction
> KQ.KBase = F.Fraction -- Num implementation of KBase not found without this
> SQ.Relation = FO.Eq
> SQ.normalize = FO.normalize
> SQ.normalizeMapsRelatedToEQ = FP.normalizeEqLemma2
> SQ.normalizeIsRelated = FP.normalizeEqLemma1

> NonNegRational : Type
> NonNegRational = KQ.KQuot

> implementation Num NonNegRational where
>   (+) = KQ.liftBinop (+)
>   (*) = KQ.liftBinop (*)
>   fromInteger = KQ.classOf . fromInteger

> implementation Show NonNegRational where
>   show (Class (n,(Element d _)) _) = show n ++ "/" ++ show d

> Fraction : Type
> Fraction = F.Fraction

> fromFraction : NonNegRational2.Fraction -> NonNegRational
> fromFraction = KQ.classOf

> plusInvariant : (x, x' : SQ.Base) -> (x `SQ.Relation` x') -> 
>                 (y, y' : SQ.Base) -> (y `SQ.Relation` y') -> 
>                 (x + y) `SQ.Relation` (x' + y')
> plusInvariant x x' xRx' y y' yRy' = plusPreservesEq x x' y y' xRx' yRy'

> multInvariant : (x, x' : SQ.Base) -> (x `SQ.Relation` x') -> 
>                 (y, y' : SQ.Base) -> (y `SQ.Relation` y') -> 
>                 (x * y) `SQ.Relation` (x' * y')
> multInvariant x x' xRx' y y' yRy' = multPreservesEq x x' y y' xRx' yRy'


> ||| Addition is commutative
> plusCommutative : (x, y : NonNegRational) -> x + y = y + x
> plusCommutative x y = 
>   let rx = repr x in
>   let ry = repr y in
>   let plusC = SQ.liftBinopCompR (+) plusInvariant in
>   let fromR = KQ.classOfAfterReprIsId in
>
>   (x + y)        ={ cong {f = \w => w + y}          (sym (fromR x)) }=
>   ([rx] + y)     ={ cong {f = \w => [rx] + w}       (sym (fromR y)) }=
>   ([rx] + [ry])  ={                                   (plusC rx ry) }=
>   ([rx + ry])    ={ cong {f = \w => [w]} (FP.plusCommutative rx ry) }=
>   ([ry + rx])    ={                               sym (plusC ry rx) }=
>   ([ry] + [rx])  ={ cong {f = \w => w + [rx]}             (fromR y) }=
>   (y + [rx])     ={ cong {f = \w => y + w}                (fromR x) }=
>   (y + x)        QED

> 
> ||| 0 is right neutral for addition
> plusZeroRightNeutral : (x : NonNegRational) -> x + 0 = x
> plusZeroRightNeutral x =
>   let rx = repr x in
>   let plusC = SQ.liftBinopCompR (+) plusInvariant in
>   let fromR = KQ.classOfAfterReprIsId in
> 
>   (x + [0])      ={ cong {f = \w => w + [0]}          (sym (fromR x)) }=
>   ([rx] + [0])   ={                                      (plusC rx 0) }=
>   ([rx + 0])     ={ cong {f = \w => [w]} (FP.plusZeroRightNeutral rx) }=
>   ([rx])         ={                                         (fromR x) }=
>   (x)            QED

> ||| 0 is left neutral for addition
> plusZeroLeftNeutral : (x : NonNegRational) -> 0 + x = x
> plusZeroLeftNeutral x =
>   (0 + x)        ={ plusCommutative 0 x    }=
>   (x + 0)        ={ plusZeroRightNeutral x }=
>   (x)            QED

> ||| Addition is associative
> plusAssociative : (x, y, z : NonNegRational) -> x + (y + z) = (x + y) + z
> plusAssociative x y z =
>   let rx = repr x in
>   let ry = repr y in
>   let rz = repr z in
>   let plusC = SQ.liftBinopCompR (+) plusInvariant in
>   let fromR = KQ.classOfAfterReprIsId in
>
>   (x + (y + z))          ={ cong {f = \w => w + (y + z)}       (sym (fromR x)) }=
>   ([rx] + (y + z))       ={ cong {f = \w => [rx] + (w + z)}    (sym (fromR y)) }=
>   ([rx] + ([ry] + z))    ={ cong {f = \w => [rx] + ([ry] + w)} (sym (fromR z)) }=
>   ([rx] + ([ry] + [rz])) ={ cong {f = \w => [rx] + w}            (plusC ry rz) }=
>   ([rx] + [ry + rz])     ={                                 plusC rx (ry + rz) }=
>   ([rx + (ry + rz)])     ={ cong {f = \w => [w]} (FP.plusAssociative rx ry rz) }=
>   ([(rx + ry) + rz])     ={                           sym (plusC (rx + ry) rz) }=
>   ([rx + ry] + [rz])     ={ cong {f = \w => w + [rz]}      (sym (plusC rx ry)) }=
>   (([rx] + [ry]) + [rz]) ={ cong {f = \w => ([rx] + [ry]) + w}       (fromR z) }=
>   (([rx] + [ry]) + z)    ={ cong {f = \w => ([rx] + w) + z}          (fromR y) }=
>   (([rx] + y) + z)       ={ cong {f = \w => (w + y) + z}             (fromR x) }=
>   ((x + y) + z)          QED
>   

Properties of |mult|:

> ||| Multiplication is commutative
> multCommutative : (x, y : NonNegRational) -> x * y = y * x
> multCommutative x y =
>   let rx = repr x in
>   let ry = repr y in
>   let multC = SQ.liftBinopCompR (*) multInvariant in
>   let fromR = KQ.classOfAfterReprIsId in
>
>   (x * y)        ={ cong {f = \w => w * y}          (sym (fromR x)) }=
>   ([rx] * y)     ={ cong {f = \w => [rx] * w}       (sym (fromR y)) }=
>   ([rx] * [ry])  ={                                   (multC rx ry) }=
>   ([rx * ry])    ={ cong {f = \w => [w]} (FP.multCommutative rx ry) }=
>   ([ry * rx])    ={                               sym (multC ry rx) }=
>   ([ry] * [rx])  ={ cong {f = \w => w * [rx]}             (fromR y) }= 
>   (y * [rx])     ={ cong {f = \w => y * w}                (fromR x) }=
>   (y * x)              QED

> ||| 1 is right neutral for multiplication
> multOneRightNeutral : (x : NonNegRational) -> x * 1 = x
> multOneRightNeutral x =
>   let rx = repr x in
>   let multC = SQ.liftBinopCompR (*) multInvariant in
>   let fromR = KQ.classOfAfterReprIsId in
> 
>   (x * [1])     ={ cong {f = \w => w * [1]}         (sym (fromR x)) }=
>   ([rx] * [1])  ={                                     (multC rx 1) }=
>   ([rx * 1])    ={ cong {f = \w => [w]} (FP.multOneRightNeutral rx) }=
>   ([rx])        ={                                        (fromR x) }=
>   (x)           QED

> ||| 1 is left neutral for multiplication
> multOneLeftNeutral : (x : NonNegRational) -> 1 * x = x
> multOneLeftNeutral x =
>   (1 * x)  ={ multCommutative 1 x   }=
>   (x * 1)  ={ multOneRightNeutral x }=
>   (x)      QED

> ||| right multiplication by zero yields zero
> multZeroRightZero : (x : NonNegRational) -> x * 0 = 0
> multZeroRightZero x =
>   let rx = repr x in
>   let multC = SQ.liftBinopCompR (*) multInvariant in
>   let fromR = KQ.classOfAfterReprIsId in
>
>   (x * [0])         ={ cong {f = \z => z * [0]}                     (sym (fromR x)) }=
>   ([rx] * [0])      ={                                                 (multC rx 0) }=
>   ([rx * 0])        ={ SQ.classOfEqIfRelated (rx * 0) 0 (FP.multZeroRightEqZero rx) }=
>   ([0])             QED

> ||| left multiplication by zero yields zero
> multZeroLeftZero : (x : NonNegRational) -> 0 * x = 0
> multZeroLeftZero x =
>   (0 * x)           ={ multCommutative 0 x }=
>   (x * 0)           ={ multZeroRightZero x }=
>   (0)               QED

> ||| multiplication distributes over addition in the right factor
> multDistributesOverPlusRight :  (x, y, z : NonNegRational) -> 
>                                 x * (y + z) = (x * y) + (x * z)
> multDistributesOverPlusRight x y z =
>   let rx = repr x in
>   let ry = repr y in
>   let rz = repr z in
>   let plusC = SQ.liftBinopCompR (+) plusInvariant in
>   let multC = SQ.liftBinopCompR (*) multInvariant in
>   let fromR = KQ.classOfAfterReprIsId in
>
>   (x * (y + z))               ={ cong {f = \w => w * (y + z)}       (sym (fromR x)) }=
>   ([rx] * (y + z))            ={ cong {f = \w => [rx] * (w + z)}    (sym (fromR y)) }=
>   ([rx] * ([ry] + z))         ={ cong {f = \w => [rx] * ([ry] + w)} (sym (fromR z)) }=
>   ([rx] * ([ry] + [rz]))      ={ cong {f = \w => [rx] * w}          (plusC ry rz)   }=
>   ([rx] * [ry + rz])          ={                                 multC rx (ry + rz) }=
>   ([rx * (ry + rz)])          ={ SQ.classOfEqIfRelated (rx * (ry + rz)) 
>                                                        ((rx * ry) + (rx * rz))
>                                                 (FP.multDistributesOverPlusRightEq) }=
>   ([(rx * ry) + (rx * rz)])   ={                    sym (plusC (rx * ry) (rx * rz)) }=
>   ([rx * ry] + [rx * rz])     ={ cong {f = \w => w + [rx * rz]} (sym (multC rx ry)) }=
>   (([rx] * [ry]) + [rx * rz]) ={ cong {f = \w => (w * [ry]) + [rx * rz]}  (fromR x) }=
>   ((x * [ry]) + [rx * rz])    ={ cong {f = \w => (x * w) + [rx * rz]}     (fromR y) }=
>   ((x * y) + [rx * rz])       ={ cong {f = \w => (x * y) + w}   (sym (multC rx rz)) }=
>   ((x * y) + ([rx] * [rz]))   ={ cong {f = \w => (x * y) + (w * [rz])}    (fromR x) }=
>   ((x * y) + (x * [rz]))      ={ cong {f = \w => (x * y) + (x * w)}       (fromR z) }=
>   ((x * y) + (x * z))         QED


> ||| multiplication distributes over addition in the left factor
> multDistributesOverPlusLeft : (x, y, z : NonNegRational) -> 
>                               (x + y) * z = (x * z) + (y * z)
> multDistributesOverPlusLeft x y z =
>     ( (x + y) * z )   ={                        multCommutative (x + y) z }=
>     ( z * (x + y) )   ={               multDistributesOverPlusRight z x y }=
>     ( z * x + z * y ) ={ cong {f = \w => w + z * y} (multCommutative z x) }=
>     ( x * z + z * y ) ={ cong {f = \w => x * z + w} (multCommutative z y) }=
>     ( x * z + y * z ) QED  

> ||| NonNegRational is an implementation of NumPlusZeroNeutral
> implementation NumPlusZeroNeutral NonNegRational where
>   plusZeroLeftNeutral = plusZeroLeftNeutral
>   plusZeroRightNeutral = plusZeroRightNeutral


> ||| NonNegRational is an implementation of NumPlusAssociative
> implementation NumPlusAssociative NonNegRational where
>   plusAssociative = plusAssociative


> ||| NonNegRational is an implementation of NumMultZeroOne
> implementation NumMultZeroOne NonNegRational where
>   multZeroRightZero   = multZeroRightZero
>   multZeroLeftZero    = multZeroLeftZero
>   multOneRightNeutral = multOneRightNeutral
>   multOneLeftNeutral  = multOneLeftNeutral


> ||| NonNegRational is an implementation NumMultDistributesOverPlus
> implementation NumMultDistributesOverPlus NonNegRational where
>   multDistributesOverPlusRight = multDistributesOverPlusRight
>   multDistributesOverPlusLeft  = multDistributesOverPlusLeft

