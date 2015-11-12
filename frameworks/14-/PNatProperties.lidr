> module PNat

> import Syntax.PreorderReasoning

> import PNat
> import PNatOperations
> import Unique
> import SubsetProperties


> %default total


> |||
> multCommutative : (m : PNat) -> (n : PNat) -> m * n = n * m
> multCommutative (Element m pm) (Element n pn) =
>     ( Element (m * n) (multPreservesIsSucc pm pn) )
>   ={ subsetEqLemma1 (Element (m * n) (multPreservesIsSucc pm pn))
>                     (Element (n * m) (multPreservesIsSucc pn pm))
>                     (multCommutative m n) 
>                     IsSuccUnique  }=
>     ( Element (n * m) (multPreservesIsSucc pn pm) )
>   QED



