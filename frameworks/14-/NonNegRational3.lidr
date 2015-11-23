> module NonNegRational3

> import NatPositive
> import PNat
> import Fraction as F
> import FractionOperations as FO
> import FractionProperties as FP
> import SplitQuotient as SQ
> import KernelQuotient as KQ
> import Syntax.PreorderReasoning

> %default total

> SQ.Base = F.Fraction
> KQ.KBase = F.Fraction -- why is this needed?
> SQ.Relation = FO.Eq
> SQ.normalize = FO.normalize
> SQ.normalizeMapsRelatedToEQ = FP.normalizeEqLemma2
> SQ.normalizeIsRelated = FP.normalizeEqLemma1

> Rational : Type
> Rational = KQ.KQuot

> toRat : (n, d : Nat) -> Rational
> toRat n (S d) = [ f2 ] where
>   d' : PNat
>   d' = (Element (S d) MkPositive)
>   f : Fraction
>   f = (n , d')
>   f1 : SQ.Base
>   f1 = f
>   f2 : KQ.KBase
>   f2 = f1

test numbers

> elevenThirds : Rational
> elevenThirds = [ ( 11 , (Element 3 MkPositive)) ]

> sevenHalfs : Rational
> sevenHalfs = [ ( 28, (Element 8 MkPositive)) ] 


> elevenThirds' : KQ.KQuot
> elevenThirds' = [ ( 11 , (Element 3 MkPositive)) ]

> sevenHalfs' : KQ.KQuot
> sevenHalfs' = [ ( 28, (Element 8 MkPositive)) ] 

> instance Num Rational where
>   (+) = KQ.liftBinop (+)
>   (*) = KQ.liftBinop (*)
>   fromInteger = KQ.classOf . fromInteger


> plusInvariant : (x, x' : SQ.Base) -> (x `SQ.Relation` x') -> 
>                 (y, y' : SQ.Base) -> (y `SQ.Relation` y') -> 
>                 (x + y) `SQ.Relation` (x' + y')
> plusInvariant x x' xRx' y y' yRy' = plusPreservesEq x x' y y' xRx' yRy'

> multInvariant : (x, x' : SQ.Base) -> (x `SQ.Relation` x') -> 
>                 (y, y' : SQ.Base) -> (y `SQ.Relation` y') -> 
>                 (x * y) `SQ.Relation` (x' * y')
> multInvariant x x' xRx' y y' yRy' = multPreservesEq x x' y y' xRx' yRy'


> ||| Addition is commutative
> plusCommutative : (x : Rational) -> (y : Rational) -> x + y = y + x
> plusCommutative x y = 
>   let rx = repr x in
>   let ry = repr y in
>
>   (x + y)             ={ SQ.liftBinopCompR1 (+) plusInvariant x y                     }=
>   ([rx + ry])         ={ cong {f = \z => [z]} (FP.plusCommutative rx ry)              }=
>   ([ry + rx])         ={ sym (SQ.liftBinopCompR1 (+) plusInvariant y x)               }=
>   (y + x)             QED

> 
> ||| |fromInteger 0| is neutral element of addition
> plusZeroRightNeutral : (x : Rational) -> x + (fromInteger 0) = x
> plusZeroRightNeutral x =
>   let rx = repr x in
> 
>   (x + [fromInteger 0])     ={ cong {f = \z => z + [fromInteger 0]} (sym (KQ.classOfAfterReprIsId x)) }=
>   ([rx] + [fromInteger 0])  ={ SQ.liftBinopCompR (+) plusInvariant rx (fromInteger 0)                 }=
>   ([rx + (fromInteger 0)])  ={ cong {f = \z => [z]} (FP.plusZeroRightNeutral rx)                      }=
>   ([rx])                    ={ KQ.classOfAfterReprIsId x                                              }=
>   (x)                       QED

> ||| |fromInteger 0| is neutral element of addition
> plusZeroLeftNeutral : (x : Rational) -> (fromInteger 0) + x = x
> plusZeroLeftNeutral x =
>   let rx = repr x in
> 
>   ([fromInteger 0] + x)     ={ cong {f = \z => [fromInteger 0] + z} (sym (KQ.classOfAfterReprIsId x)) }=
>   ([fromInteger 0] + [rx])  ={ SQ.liftBinopCompR (+) plusInvariant  (fromInteger 0) rx                }=
>   ([(fromInteger 0) + rx])  ={ cong {f = \z => [z]} (FP.plusZeroLeftNeutral rx)                       }=
>   ([rx])                    ={ KQ.classOfAfterReprIsId x                                              }=
>   (x)                       QED

> ||| Addition is associative
> plusAssociative : (x : Rational) -> (y : Rational) -> (z : Rational) -> x + (y + z) = (x + y) + z
> plusAssociative x y z =
>   let rx = repr x in
>   let ry = repr y in
>   let rz = repr z in
>
>   (x + (y + z))          ={ cong {f = \w => w + (y + z)}       (sym (KQ.classOfAfterReprIsId x))     }=
>   ([rx] + (y + z))       ={ cong {f = \w => [rx] + (w + z)}    (sym (KQ.classOfAfterReprIsId y))     }=
>   ([rx] + ([ry] + z))    ={ cong {f = \w => [rx] + ([ry] + w)} (sym (KQ.classOfAfterReprIsId z))     }=
>   ([rx] + ([ry] + [rz])) ={ cong {f = \w => [rx] + w} (liftBinopCompR (+) plusInvariant ry rz)       }=
>   ([rx] + [ry + rz])     ={ liftBinopCompR (+) plusInvariant rx (ry + rz)                            }=
>   ([rx + (ry + rz)])     ={ cong {f = \w => [w]} (FP.plusAssociative rx ry rz)                       }=
>   ([(rx + ry) + rz])     ={ sym (liftBinopCompR (+) plusInvariant (rx + ry) rz)                      }=
>   ([rx + ry] + [rz])     ={ cong {f = \w => w + [rz]} (sym (liftBinopCompR (+) plusInvariant rx ry)) }=
>   (([rx] + [ry]) + [rz]) ={ cong {f = \w => ([rx] + [ry]) + w} (KQ.classOfAfterReprIsId z)           }=
>   (([rx] + [ry]) + z)    ={ cong {f = \w => ([rx] + w) + z}    (KQ.classOfAfterReprIsId y)           }=
>   (([rx] + y) + z)       ={ cong {f = \w => (w + y) + z}       (KQ.classOfAfterReprIsId x)           }=
>   ((x + y) + z)          QED
>   

Properties of |mult|:

> multCommutative : (x : Rational) -> (y : Rational) -> x * y = y * x
> multCommutative x y =
>   let rx = repr x in
>   let ry = repr y in
>
>   (x * y)             ={ SQ.liftBinopCompR1 (*) multInvariant x y                     }=
>   ([rx * ry])         ={ cong {f = \z => [z]} (FP.multCommutative rx ry)              }=
>   ([ry * rx])         ={ sym (SQ.liftBinopCompR1 (*) multInvariant y x)               }=
>   (y * x)             QED

