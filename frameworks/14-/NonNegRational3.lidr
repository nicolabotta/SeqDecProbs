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


> plusInvariant : (x, x', y, y' : SQ.Base) -> (x `SQ.Relation` y) -> (x' `SQ.Relation` y') -> [ x + x' ] = [ y + y' ]

> multInvariant : (x, x', y, y' : SQ.Base) -> (x `SQ.Relation` y) -> (x' `SQ.Relation` y') -> [ x * x' ] = [ y * y' ]


> ||| Addition is commutative
> plusCommutative : (x : Rational) -> (y : Rational) -> x + y = y + x
> plusCommutative x y = 
>   let rx = repr x in
>   let ry = repr y in
>
>   (x + y)             ={ cong {f = \z => z + y}    (sym (KQ.classOfAfterReprIsId x))  }=
>   ([rx] + y)          ={ cong {f = \z => [rx] + z} (sym (KQ.classOfAfterReprIsId y))  }=
>   ([rx] + [ry])       ={ SQ.liftBinopCompR (+) plusInvariant rx ry                    }=
>   ([rx + ry])         ={ cong {f = \z => [ z ]} (FP.plusCommutative rx ry)            }=
>   ([ry + rx])         ={ sym (SQ.liftBinopCompR (+) plusInvariant ry rx)              }=
>   ([ry] + [rx])       ={ cong {f = \z => [ry] + z} (KQ.classOfAfterReprIsId x)        }=
>   ([ry] + x)          ={ cong {f = \z => z + x}    (KQ.classOfAfterReprIsId y)        }=
>   (y + x)             QED

> 


