> module PNat

> import Syntax.PreorderReasoning

> import PNat
> import PNatOperations
> import NatPositive
> import Unique
> import SubsetProperties
> import NatProperties
> import PairsOperations


> %default total

> %access public export


> ||| PNat is an implementation of Show
> implementation Show PNat where
>   show = show . toNat


> |||
> predToNatLemma : (x : PNat) -> S (pred x) = toNat x
> predToNatLemma (Element _ (MkPositive {n})) = Refl


> |||
> toNatfromNatLemma : (m : Nat) -> (zLTm : Z `LT` m) -> toNat (fromNat m zLTm) = m
> toNatfromNatLemma m zLTm = Refl
> %freeze toNatfromNatLemma


> |||
> toNatLTLemma : (x : PNat) -> Z `LT` toNat x
> toNatLTLemma x = s2 where
>   s1 : Z `LT` (S (pred x))
>   s1 = ltZS (pred x)
>   s2 : Z `LT` (toNat x)
>   s2 = replace (predToNatLemma x) s1
> %freeze toNatLTLemma


> ||| 
> toNatEqLemma : {x, y : PNat} -> (toNat x) = (toNat y) -> x = y
> toNatEqLemma {x} {y} p = subsetEqLemma1 x y p PositiveUnique
> %freeze toNatEqLemma


> ||| 
> toNatMultLemma : {x, y : PNat} -> toNat (x * y) = (toNat x) * (toNat y)
> toNatMultLemma {x = (Element m pm)} {y = (Element n pn)} = Refl
> %freeze toNatMultLemma


> |||
> multOneRightNeutral : (x : PNat) -> x * (Element 1 MkPositive) = x
> multOneRightNeutral (Element m pm) =
>     ( (Element m pm) * (Element 1 MkPositive) )
>   ={ Refl }=
>     ( Element (m * 1) (multPreservesPositivity pm MkPositive) )
>   ={ toNatEqLemma (multOneRightNeutral m) }=
>     ( Element m pm )
>   QED
> %freeze multOneRightNeutral


> |||
> multCommutative : (x : PNat) -> (y : PNat) -> x * y = y * x
> multCommutative (Element m pm) (Element n pn) =
>   let pmn = multPreservesPositivity pm pn in
>   let pnm = multPreservesPositivity pn pm in
>     ( Element (m * n) pmn )
>   ={ toNatEqLemma (multCommutative m n) }=
>     ( Element (n * m) pnm )
>   QED
> %freeze multCommutative


> |||
> multAssociative : (x : PNat) -> (y : PNat) -> (z : PNat) -> x * (y * z) = (x * y) * z
> multAssociative (Element m pm) (Element n pn) (Element o po) = 
>   let pno   = multPreservesPositivity pn po  in
>   let pmno  = multPreservesPositivity pm pno in
>   let pmn   = multPreservesPositivity pm pn  in
>   let pmno' = multPreservesPositivity pmn po in
>     ( (Element m pm) * ((Element n pn) * (Element o po)) )
>   ={ Refl }=
>     ( (Element m pm) * (Element (n * o) pno) )
>   ={ Refl }=
>     ( Element (m * (n * o)) pmno )
>   -- ={ toNatEqLemma (multAssociative m n o) }=
>   ={ toNatEqLemma (Prelude.Nat.multAssociative m n o) }=
>     ( Element ((m * n) * o) pmno' )
>   ={ Refl }=
>     ( (Element (m * n) pmn) * (Element o po) )
>   ={ Refl }=
>     ( ((Element m pm) * (Element n pn)) * (Element o po) )
>   QED
> %freeze multAssociative
