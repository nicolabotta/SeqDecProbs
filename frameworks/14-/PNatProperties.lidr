> module PNat

> import Syntax.PreorderReasoning

> import PNat
> import PNatOperations
> import Unique
> import SubsetProperties
> import NatProperties


> %default total


> |||
> predToNatLemma : (x : PNat) -> S (pred x) = toNat x
> predToNatLemma (Element _ (MkIsSucc {n})) = Refl


> |||
> toNatLTLemma : (x : PNat) -> Z `LT` toNat x
> toNatLTLemma x = s2 where
>   s1 : Z `LT` (S (pred x))
>   s1 = ltZS (pred x)
>   s2 : Z `LT` (toNat x)
>   s2 = replace (predToNatLemma x) s1


> ||| 
> toNatEqLemma : {x, y : PNat} -> (toNat x) = (toNat y) -> x = y
> toNatEqLemma {x} {y} p = subsetEqLemma1 x y p IsSuccUnique
> %freeze toNatEqLemma


> ||| 
> toNatMultLemma : {x, y : PNat} -> toNat (x * y) = (toNat x) * (toNat y)
> toNatMultLemma {x = (Element m pm)} {y = (Element n pn)} = Refl
> %freeze toNatMultLemma


> |||
> multOneRightNeutral : (x : PNat) -> x * (Element 1 MkIsSucc) = x
> multOneRightNeutral (Element m pm) =
>     ( (Element m pm) * (Element 1 MkIsSucc) )
>   ={ Refl }=
>     ( Element (m * 1) (multPreservesIsSucc pm MkIsSucc) )
>   ={ toNatEqLemma (multOneRightNeutral m) }=
>     ( Element m pm )
>   QED
> %freeze multOneRightNeutral


> |||
> multCommutative : (x : PNat) -> (y : PNat) -> x * y = y * x
> multCommutative (Element m pm) (Element n pn) =
>   let pmn = multPreservesIsSucc pm pn in
>   let pnm = multPreservesIsSucc pn pm in
>     ( Element (m * n) pmn )
>   ={ toNatEqLemma (multCommutative m n) }=
>     ( Element (n * m) pnm )
>   QED
> %freeze multCommutative


> |||
> multAssociative : (x : PNat) -> (y : PNat) -> (z : PNat) -> x * (y * z) = (x * y) * z
> multAssociative (Element m pm) (Element n pn) (Element o po) = 
>   let pno   = multPreservesIsSucc pn po  in
>   let pmno  = multPreservesIsSucc pm pno in
>   let pmn   = multPreservesIsSucc pm pn  in
>   let pmno' = multPreservesIsSucc pmn po in
>     ( (Element m pm) * ((Element n pn) * (Element o po)) )
>   ={ Refl }=
>     ( (Element m pm) * (Element (n * o) pno) )
>   ={ Refl }=
>     ( Element (m * (n * o)) pmno )
>   ={ toNatEqLemma (multAssociative m n o) }=
>     ( Element ((m * n) * o) pmno' )
>   ={ Refl }=
>     ( (Element (m * n) pmn) * (Element o po) )
>   ={ Refl }=
>     ( ((Element m pm) * (Element n pn)) * (Element o po) )
>   QED
> %freeze multAssociative
