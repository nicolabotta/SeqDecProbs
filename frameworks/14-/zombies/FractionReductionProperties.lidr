> module FractionReductionProperties

> import Syntax.PreorderReasoning

> import FractionReduction
> import FractionReductionOperations
> import Fraction
> import FractionOperations
> import PNat
> import PNatOperations
> import PNatProperties
> import Basics
> import NatProperties
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
> import SubsetProperties
> import Unique


> %default total


> fromNatReduced : (n : Nat) -> Reduced (fromNat n)
> fromNatReduced n = MkReduced anyCoprimeOne
> %freeze fromNatReduced


> ||| Reduction of reduced fractions is identity
> reducePreservesReduced : (x : Subset Fraction Reduced) -> reduce (getWitness x) = x                       
> reducePreservesReduced (Element (m, n') (MkReduced (MkCoprime prf))) =
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
>   let zLTd    :  (Z `LT` d)
>               =  gcdPreservesPositivity2 zLTn (d ** dGCDmn) in
>   let dEQ1    :  (d = S Z)
>               =  prf in
>   let lala    :  ((o, fromNat p zLTp) = (m, n'))
>               =  cong2 (quotientAnyOneAny m d dDm dEQ1) (toNatEqLemma (quotientAnyOneAny n d dDn dEQ1)) in
>             
>     ( reduce (m, n') )
>   ={ Refl }=
>     ( Element (o, fromNat p zLTp) (MkReduced (gcdCoprimeLemma d m n dDm dDn zLTd dGCDmn)) )
>   ={ subsetEqLemma1 (Element (o, fromNat p zLTp) (MkReduced (gcdCoprimeLemma d m n dDm dDn zLTd dGCDmn))) 
>                     (Element (m, n') (MkReduced (MkCoprime prf))) 
>                     lala 
>                     ReducedUnique }=
>     ( Element (m, n') (MkReduced (MkCoprime prf)) )
>   QED
> %freeze reducePreservesReduced


> {-

> ||| 
> reduceReduces : (x : Fraction) -> Reduced (reduce x)
> reduceReduces (m, n') =
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
>               =  gcdPreservesPositivity2 zLTn (d ** dGCDmn) in
>   MkReduced (gcdCoprimeLemma d m n dDm dDn zLTd dGCDmn)
> %freeze reduceReduces


> ||| Reduction of coprime numbers is identity
> reducePreservesReduced : (x : Fraction) -> Reduced x -> reduce x = x                       
> reducePreservesReduced (m, n') (MkReduced (MkCoprime prf)) =
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
>     ( reduce (m, n') )
>   ={ Refl }=
>     ( (o, fromNat p zLTp) )
>   ={ cong2 (quotientAnyOneAny m d dDm dEQ1) (toNatEqLemma (quotientAnyOneAny n d dDn dEQ1)) }=
>     ( (m, n') )
>   QED
> %freeze reducePreservesReduced


> ||| Reduction is idempotent
> reduceIdempotent : (x : Fraction) -> reduce (reduce x) = reduce x
> reduceIdempotent x = 
>     ( reduce (reduce x) )
>   ={ reducePreservesReduced (reduce x) (reduceReduces x) }=
>     ( reduce x )
>   QED
> %freeze reduceIdempotent

> ---}

 
