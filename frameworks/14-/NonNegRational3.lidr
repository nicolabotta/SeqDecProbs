> module NonNegRational3

> import NatPositive
> import PNat
> import Fraction as F
> import FractionOperations as FO
> import FractionProperties as FP
> import SplitQuotient as SQ
> import KernelQuotient as KQ

> %default total

> SQ.Base = F.Fraction
> KQ.KBase = F.Fraction -- why is this needed?
> SQ.Relation = FO.Eq
> SQ.normalize = FO.normalize
> SQ.normalizeMapsRelatedToEQ = FP.normalizeEqLemma2
> SQ.normalizeIsRelated = FP.normalizeEqLemma1

> Rational : Type
> Rational = SQ.Quot

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
