> module NonNegRationalLTEProperties

> import Syntax.PreorderReasoning

> import NonNegRational
> import NonNegRationalBasicOperations
> import NonNegRationalBasicProperties
> import NonNegRationalPredicates
> import Fraction
> import FractionBasicOperations
> import FractionPredicates
> import FractionBasicProperties
> import FractionNormalize
> import FractionNormalizeProperties
> import FractionEqProperties
> import FractionLTEProperties
> import FractionNormal
> import SubsetProperties
> import Unique
> import NatPositive
> import NumRefinements
> import PairsOperations
> import NatLTEProperties
> import NatOperationsProperties
> -- import ListProperties 
 
> %default total
> %access public export


|LTE| is a total preorder:

> ||| LTE is reflexive
> reflexiveLTE : (x : NonNegRational) -> x `LTE` x
> reflexiveLTE x = reflexiveLTE (toFraction x)
> %freeze reflexiveLTE


> ||| LTE is transitive
> transitiveLTE : (x, y, z : NonNegRational) -> x `LTE` y -> y `LTE` z -> x `LTE` z
> transitiveLTE x y z xLTEy yLTEz = transitiveLTE (toFraction x) (toFraction y) (toFraction z) xLTEy yLTEz
> %freeze transitiveLTE


> ||| LTE is total
> totalLTE : (x, y : NonNegRational) -> Either (x `LTE` y) (y `LTE` x) 
> totalLTE x y = totalLTE (toFraction x) (toFraction y)
> %freeze totalLTE


Properties of |LTE| and |plus|:

> ||| LTE is monotone w.r.t. `plus`
> monotonePlusLTE : {a, b, c, d : NonNegRational} -> 
>                   a `LTE` b -> c `LTE` d -> (a + c) `LTE` (b + d)
> monotonePlusLTE {a} {b} {c} {d} aLTEb cLTEd = s4 where
>   s1 : LTE (toFraction a + toFraction c) (toFraction b + toFraction d)
>   s1 = FractionLTEProperties.monotonePlusLTE aLTEb cLTEd
>   s2 : LTE (normalize (toFraction a + toFraction c)) 
>            (normalize (toFraction b + toFraction d))
>   s2 = normalizeLTELemma (toFraction a + toFraction c) (toFraction b + toFraction d) s1
>   s3 : LTE (toFraction (fromFraction (toFraction a + toFraction c)))
>            (toFraction (fromFraction (toFraction b + toFraction d)))
>   s3 = s2
>   s4 : LTE (fromFraction (toFraction a + toFraction c)) (fromFraction (toFraction b + toFraction d))
>   s4 = s3
>   s5 : LTE (a + c) (b + d)
>   s5 = s4
> %freeze monotonePlusLTE


Properties of |LTE| and |mult|:

> ||| LTE is monotone w.r.t. `(*)`
> monotoneMultLTE : {a, b, c, d : NonNegRational} -> 
>                   a `LTE` b -> c `LTE` d -> (a * c) `LTE` (b * d)
> monotoneMultLTE {a} {b} {c} {d} aLTEb cLTEd = s4 where
>   s1 : LTE (toFraction a * toFraction c) (toFraction b * toFraction d)
>   s1 = FractionLTEProperties.monotoneMultLTE aLTEb cLTEd
>   s2 : LTE (normalize (toFraction a * toFraction c)) 
>            (normalize (toFraction b * toFraction d))
>   s2 = normalizeLTELemma (toFraction a * toFraction c) (toFraction b * toFraction d) s1
>   s3 : LTE (toFraction (fromFraction (toFraction a * toFraction c)))
>            (toFraction (fromFraction (toFraction b * toFraction d)))
>   s3 = s2
>   s4 : LTE (fromFraction (toFraction a * toFraction c)) (fromFraction (toFraction b * toFraction d))
>   s4 = s3
>   s5 : LTE (a * c) (b * d)
>   s5 = s4
> %freeze monotoneMultLTE


> {-

> ---}
 
