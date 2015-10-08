> module NonNegRationalProperties

> import Syntax.PreorderReasoning

> import NonNegRational
> import NonNegRationalOperations
> import NatPredicates
> import NatOperations
> import NatProperties
> import Basics
> import NumRefinements
> import GCD
> import EqualityProperties
> import Fraction


> %default total


> ||| Non-negative rationals are in |Show|
> instance Show NonNegQ where
>   show q = show (num q) ++ "/" ++ show (den q)

> ||| Non-negative rationals are in |Num|
> instance Num NonNegQ where
>   (+) = plus
>   (*) = mult
>   fromInteger = NonNegRationalOperations.fromNat . fromIntegerNat


Properties of |num|, |den|:

> -- denPreservesEquality : (q1 : NonNegQ) -> (q2 : NonNegQ) -> q1 = q2 -> den q1 = den q2
> -- denPreservesEquality (MkNonNegQ n d p q) (MkNonNegQ n d p q) Refl = Refl

> ||| The numerator of zero is zero
> numZeroZero : NonNegRationalOperations.num (fromInteger 0) = Z
> numZeroZero = ( NonNegRationalOperations.num (fromInteger 0) )
>             ={ Refl }=
>               ( NonNegRationalOperations.num (fromNat (fromIntegerNat 0)) )
>             ={ Refl }=
>               ( NonNegRationalOperations.num (fromNat Z) )
>             ={ Refl }=
>               ( NonNegRationalOperations.num (MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z)) )
>             ={ Refl }=
>               ( Z )
>             QED
> %freeze numZeroZero

> -- denZeroOne : den (fromInteger 0) = S Z


Properties of casts:

> ||| 
> fromFractionLemma : (x : Fraction) -> 
>                     (zLTden : Z `LT` den x) ->
>                     (gcdOne : gcd (alg (num x) (den x)) = S Z) ->
>                     fromFraction x zLTden = MkNonNegQ (num x) (den x) zLTden gcdOne
> fromFractionLemma x zLTden gcdOne = 
>    ( fromFraction x zLTden )
>  ={ Refl }=
>    ( MkNonNegQ (num (reduce alg x)) 
>                (den (reduce alg x)) 
>                (reducePreservesPositivity alg x zLTden) 
>                (reduceYieldsCoprimes alg x zLTden) )
>  ={ ?gugu }=
>    ( MkNonNegQ (num x) (den x) zLTden gcdOne )
>  QED

> 
> {-
> with (decEq (gcd (alg n d)) (S Z))
>   | (Yes prf)   = ( MkNonNegQ n d zLTd prf )
>                 ={ replace {x = prf}
>                            {y = gcdOne}
>                            {P = \ ZUZU => MkNonNegQ n d zLTd prf = MkNonNegQ n d zLTd ZUZU}
>                            (uniqueEq (gcd (alg n d)) (S Z) prf gcdOne)
>                            Refl }=
>                   ( MkNonNegQ n d zLTd gcdOne )
>                 QED
>   | (No contra) = void (contra gcdOne)
> -}


> fromFractionToFractionLemma : 
>   (q : NonNegQ) -> 
>   fromFraction (toFraction q) (toFractionPreservesDenominatorPositivity q) = q
> -- fromFractionToFractionLemma q 
> %freeze fromFractionToFractionLemma


> ||| fromFraction preserves identity
> fromFractionLemma2 : 
>   (x : Fraction) -> 
>   (zLTdx : Z `LT` den x) ->
>   (y : Fraction) -> 
>   (zLTdy : Z `LT` den y) ->
>   x = y -> 
>   fromFraction x zLTdx = fromFraction y zLTdy
> fromFractionLemma2 x zLTdx y zLTdy xEQy =
>     ( fromFraction x zLTdx )
>   ={ depCong2' {alpha = Fraction}
>                {P = \ ZUZU => Z `LT` (den ZUZU)}
>                {Q = \ ZUZU => \ zLTdenZUZU => NonNegQ}
>                {a1 = x}
>                {a2 = y}
>                {Pa1 = zLTdx}
>                {Pa2 = zLTdy}
>                (\ ZUZU => \ zLTdenZUZU => fromFraction ZUZU zLTdenZUZU)
>                xEQy (uniqueLT' Refl (denPreservesEquality x y xEQy) zLTdx zLTdy) }=
>     ( fromFraction y zLTdy )
>   QED
> %freeze fromFractionLemma2


> ||| fromFraction is "linear"
> fromFractionLinear : 
>   (x : Fraction) -> 
>   (zLTdx : Z `LT` den x) ->
>   (y : Fraction) -> 
>   (zLTdy : Z `LT` den y) ->
>   fromFraction (x + y) (plusPreservesPositivity x y zLTdx zLTdy)
>   =
>   fromFraction x zLTdx + fromFraction y zLTdy
> %freeze fromFractionLinear


> ||| Addition is commutative
> plusCommutative : (x : NonNegQ) -> (y : NonNegQ) -> x + y = y + x
> plusCommutative x y = 
>   let x' = toFraction x in
>   let y' = toFraction y in
>   let zLTdx' = toFractionPreservesDenominatorPositivity x in
>   let zLTdy' = toFractionPreservesDenominatorPositivity y in
>   let zLTdx'y' = plusPreservesPositivity x' y' zLTdx' zLTdy' in
>   let zLTdy'x' = plusPreservesPositivity y' x' zLTdy' zLTdx' in
>     ( x + y )
>   ={ Refl }=
>     ( fromFraction (x' + y') zLTdx'y' )
>   ={ fromFractionLemma2 (x' + y') zLTdx'y' (y' + x') zLTdy'x' (plusCommutative x' y') }=
>     ( fromFraction (y' + x') (plusPreservesPositivity y' x' zLTdy' zLTdx') )    
>   ={ Refl }=
>     ( y + x )
>   QED
> %freeze plusCommutative


> ||| Addition is associative
> plusAssociative : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) -> x + (y + z) = (x + y) + z
> plusAssociative x y z = 
>   let x' = toFraction x in
>   let y' = toFraction y in
>   let z' = toFraction z in
>   let zLTdx' = toFractionPreservesDenominatorPositivity x in
>   let zLTdy' = toFractionPreservesDenominatorPositivity y in
>   let zLTdz' = toFractionPreservesDenominatorPositivity z in
>   let zLTdyz' = toFractionPreservesDenominatorPositivity (y + z) in
>   let zLTdx'yz' = plusPreservesPositivity (toFraction x) (toFraction (y + z)) zLTdx' zLTdyz' in
>   
>   let zLTdy'z' = plusPreservesPositivity (toFraction y) (toFraction z) zLTdy' zLTdz' in
>   let zLTdx'py'z' = plusPreservesPositivity (toFraction x) (toFraction y + toFraction z) zLTdx' zLTdy'z' in
>   let zLTdx'y' = plusPreservesPositivity (toFraction x) (toFraction y) zLTdx' zLTdy' in
>   let zLTdx'y'pz' = plusPreservesPositivity (toFraction x + toFraction y) (toFraction z) zLTdx'y' zLTdz' in
>   
>     ( x + (y + z) )
>   ={ Refl }=
>     ( fromFraction (toFraction x + toFraction (y + z)) zLTdx'yz' )
>   ={ fromFractionLinear (toFraction x) zLTdx' (toFraction (y + z)) zLTdyz' }=
>     ( fromFraction (toFraction x) zLTdx' + fromFraction (toFraction (y + z)) zLTdyz' )  
>   ={ replace {x = fromFraction (toFraction (y + z)) zLTdyz'}
>              {y = y + z}
>              {P = \ ZUZU => fromFraction (toFraction x) zLTdx' + fromFraction (toFraction (y + z)) zLTdyz'
>                             =
>                             fromFraction (toFraction x) zLTdx' + ZUZU}
>              (fromFractionToFractionLemma (y + z)) Refl }=
>     ( fromFraction (toFraction x) zLTdx' + (y + z) )  
>   ={ Refl }=
>     ( fromFraction (toFraction x) zLTdx' + fromFraction (toFraction y + toFraction z) zLTdy'z' )
>   ={ sym (fromFractionLinear (toFraction x) zLTdx' (toFraction y + toFraction z) zLTdy'z') }=
>     ( fromFraction (toFraction x + (toFraction y + toFraction z)) zLTdx'py'z' )  
>   ={ fromFractionLemma2 (toFraction x + (toFraction y + toFraction z)) 
>                         zLTdx'py'z' 
>                         ((toFraction x + toFraction y) + toFraction z) 
>                         zLTdx'y'pz' 
>                         (plusAssociative (toFraction x) (toFraction y) (toFraction z)) }=
>     ( fromFraction ((toFraction x + toFraction y) + toFraction z) zLTdx'y'pz' )    
>   ={ ?proof_in_reverse }=
>     ( (x + y) + z )
>   QED
> %freeze plusAssociative

> {-

> fromFractionLemma2 : (n : Nat) -> (d : Nat) -> (zLTd : Z `LT` d) ->
>                      (n' : Nat) -> (d' : Nat) -> (zLTd' : Z `LT` d') ->
>                      n = n' -> d = d' ->
>                      fromFraction n d zLTd = fromFraction n' d' zLTd'
> fromFractionLemma2 n d zLTd n' d' zLTd' nEQn' dEQd' = trans s2 s3 where
>   s1 : zLTd = zLTd'
>   s1 = uniqueLT' Refl dEQd' zLTd zLTd'
>   s2 : fromFraction n d zLTd = fromFraction n' d zLTd
>   s2 = replace {x = n}
>                {y = n'}
>                {P = \ ZUZU => fromFraction n d zLTd = fromFraction ZUZU d zLTd}
>                nEQn' Refl
>   s3 : fromFraction n' d zLTd = fromFraction n' d' zLTd'
>   s3 = depCong2' {alpha = Nat}
>                  {P = \ ZUZU => Z `LT` ZUZU}
>                  {Q = \ ZUZU => \ zLTZUZU => NonNegQ}
>                  {a1 = d}
>                  {a2 = d'}
>                  {Pa1 = zLTd}
>                  {Pa2 = zLTd'}
>                  (\ ZUZU => \ zLTZUZU => fromFraction n' ZUZU zLTZUZU)
>                  dEQd' s1

> fromFractionNumLemma : (n : Nat) -> (d : Nat) -> (zLTd : Z `LT` d) -> 
>                        num (fromFraction n d zLTd) * (gcd (alg n d)) = n

> fromFractionDenLemma : (n : Nat) -> (d : Nat) -> (zLTd : Z `LT` d) -> 
>                        den (fromFraction n d zLTd) * (gcd (alg n d)) = d

In order to implement simple probability distributions based on
non-negative rational numbers, we need these to fulfill

> plusZeroPlusRight : (x : NonNegQ) -> x + (fromInteger 0) = x
> plusZeroPlusRight (MkNonNegQ n d zLTd gcdOne) = s7 where
>   s1 : (MkNonNegQ n d zLTd gcdOne) + (fromInteger 0)
>        =
>        (MkNonNegQ n d zLTd gcdOne) + MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z)
>   s1 = Refl
>   s2 : (MkNonNegQ n d zLTd gcdOne) + MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z)
>        =
>        fromFraction (n * (S Z) + Z * d)
>                     (d * (S Z))
>                     (multZeroLTZeroLT d (S Z) zLTd (ltZS Z))
>   s2 = Refl
>   s3 : n * (S Z) + Z * d = n
>   s3 = ( n * (S Z) + Z * d )
>      ={ replace {x = n * (S Z)}
>                 {y = n}
>                 {P = \ ZUZU => n * (S Z) + Z * d = ZUZU + Z * d}
>                 (multOneRightNeutral n) Refl}=
>        ( n + Z * d )
>      ={ replace {x = Z * d}
>                 {y = Z}
>                 {P = \ ZUZU => n + Z * d = n + ZUZU}
>                 (multZeroLeftZero d) Refl }=
>        ( n + Z )
>      ={ plusZeroRightNeutral n }=
>        ( n )
>      QED
>   s4 : d * (S Z) = d
>   s4 = multOneRightNeutral d
>   s5 : fromFraction (n * (S Z) + Z * d)
>                     (d * (S Z))
>                     (multZeroLTZeroLT d (S Z) zLTd (ltZS Z))
>        =
>        fromFraction n d zLTd
>   s5 = fromFractionLemma2 (n * (S Z) + Z * d) (d * (S Z))
>                           (multZeroLTZeroLT d (S Z) zLTd (ltZS Z))
>                           n d zLTd s3 s4
>   s6 : fromFraction n d zLTd = MkNonNegQ n d zLTd gcdOne
>   s6 = fromFractionLemma1 n d zLTd gcdOne
>   s7 : (MkNonNegQ n d zLTd gcdOne) + (fromInteger 0) = (MkNonNegQ n d zLTd gcdOne)
>   s7 = trans s1 (trans s2 (trans s5 s6))


> {-
> plusZeroPlusLeft  : (x : NonNegQ) -> (fromInteger 0) + x = x
> plusZeroPlusLeft x@(MkNonNegQ n d zLTd gcdOne) =
>     (  (fromInteger 0) + x  )
>   ={ Refl }=
>     (  MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z)   +   MkNonNegQ n d zLTd gcdOne  )
>   ={ Refl }=
>     ( let n' = Z * d + n * (S Z)
>           d' = (S Z) * d
>           -- zLTd' : Z `LT` d'
>           zLTd' = multZeroLTZeroLT (S Z) d (zeroLTden (fromInteger 0)) zLTd
>       in  fromFraction n' d' zLTd' )
>   ={ ?pZPL }=
>     ( MkNonNegQ n d zLTd gcdOne )
>   ={ Refl }=
>      x
>   QED
> -}

> {-

TODO

> plusAssoc : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) -> x + (y + z) = (x + y) + z
> plusAssoc x y z = s11 where
>   nyz' : Nat
>   nyz' = (num y) * (den z) + (num z) * (den y)
>   dyz' : Nat
>   dyz' = (den y) * (den z)
>   zLTdyz' : Z `LT` dyz'
>   zLTdyz' = multZeroLTZeroLT (den y) (den z) (zeroLTden y) (zeroLTden z)
>   s1 : y + z = fromFraction nyz' dyz' zLTdyz'
>   s1 = Refl
>   nyz : Nat
>   nyz = num (fromFraction nyz' dyz' zLTdyz')
>   dyz : Nat
>   dyz = den (fromFraction nyz' dyz' zLTdyz')
>   nxyz1' : Nat
>   nxyz1' = (num x) * dyz + nyz * (den x)
>   dxyz1' : Nat
>   dxyz1' = (den x) * dyz
>   zLTdxyz1' : Z `LT` dxyz1'
>   zLTdxyz1' = multZeroLTZeroLT (den x) dyz (zeroLTden x) (zeroLTden (fromFraction nyz' dyz' zLTdyz'))
>   s2 : x + (y + z) = fromFraction nxyz1' dxyz1' zLTdxyz1'
>   s2 = Refl
>   
>   nxy' : Nat
>   nxy' = (num x) * (den y) + (num y) * (den x)
>   dxy' : Nat
>   dxy' = (den x) * (den y)
>   zLTdxy' : Z `LT` dxy'
>   zLTdxy' = multZeroLTZeroLT (den x) (den y) (zeroLTden x) (zeroLTden y)
>   s3 : x + y = fromFraction nxy' dxy' zLTdxy'
>   s3 = Refl
>   nxy : Nat
>   nxy = num (fromFraction nxy' dxy' zLTdxy')
>   dxy : Nat
>   dxy = den (fromFraction nxy' dxy' zLTdxy')
>   nxyz2' : Nat
>   nxyz2' = nxy * (den z) + (num z) * dxy
>   dxyz2' : Nat
>   dxyz2' = dxy * (den z)
>   zLTdxyz2' : Z `LT` dxyz2'
>   zLTdxyz2' = multZeroLTZeroLT dxy (den z) (zeroLTden (fromFraction nxy' dxy' zLTdxy')) (zeroLTden z) 
>   s2 : x + (y + z) = fromFraction nxyz2' dxyz2' zLTdxyz2'
>   s2 = Refl
>   
>   s11 : x + (y + z) = (x + y) + z
>   s11 = ?lulu
>   

> -}

> {- TODO: complete
> multZeroPlusRight : (x : NonNegQ) -> x * (fromInteger 0) = fromInteger 0
> multZeroPlusRight x@(MkNonNegQ n d zLTd gcdOne) =
>     (  x * (fromInteger 0)  )
>   ={ Refl }=
>     (  (MkNonNegQ n d zLTd gcdOne) * (MkNonNegQ Z (S Z) (ltZS Z) (gcdAnyOneOne alg Z))  )
>   ={ Refl }=
>     (  fromFraction (n * Z) (d * (S Z)) (multZeroLTZeroLT d (S Z) zLTd (zeroLTden (fromInteger 0))))
>   ={ ?foo }=
>     (  fromInteger 0  )
>   QED
> -}

> {-

> multZeroPlusLeft  : (x : NonNegQ) -> (fromInteger 0) * x = fromInteger 0

> multOneRight      : (x : NonNegQ) -> x * (fromInteger 1) = x

> multOneLeft       : (x : NonNegQ) -> (fromInteger 1) * x = x


> multDistributesOverPlusRight : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) ->
>                                x * (y + z) = (x * y) + (x * z)

> multDistributesOverPlusLeft  : (x : NonNegQ) -> (y : NonNegQ) -> (z : NonNegQ) ->
>                                (x + y) * z = (x * z) + (y * z)

> -}

> ---}
 
